/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 * 
 *   http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */


package org.apache.sysml.runtime.matrix.mapred;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;

import org.apache.hadoop.io.Writable;
import org.apache.hadoop.mapred.OutputCollector;
import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.matrix.data.AdaptivePartialBlock;
import org.apache.sysml.runtime.matrix.data.IJV;
import org.apache.sysml.runtime.matrix.data.MatrixBlock;
import org.apache.sysml.runtime.matrix.data.MatrixIndexes;
import org.apache.sysml.runtime.matrix.data.PartialBlock;
import org.apache.sysml.runtime.matrix.data.SparseBlock.Type;
import org.apache.sysml.runtime.matrix.data.TaggedAdaptivePartialBlock;
import org.apache.sysml.runtime.util.UtilFunctions;

public class ReblockBuffer 
{
	
	//default buffer size: 5M -> 5M * 3x8B = 120MB 
	public static final int DEFAULT_BUFFER_SIZE = 5000000;

	//buffer <long rowindex, long colindex, long value>
	//(pure long buffer for sort on flush) 
	private long[][] _buff = null;
	
	private int _bufflen = -1;
	private int _count = -1;
	
	private long _rlen = -1;
	private long _clen = -1;
	private int _brlen = -1;
	private int _bclen = -1;

	public ReblockBuffer( int buffersize, long rlen, long clen, int brlen, int bclen  )
	{
		_bufflen = buffersize;
		_count = 0;
		
		_buff = new long[ _bufflen ][3];
		
		_rlen = rlen;
		_clen = clen;
		_brlen = brlen;
		_bclen = bclen;
	}

	public void appendCell( long r, long c, double v )
	{
		long tmp = Double.doubleToRawLongBits(v);
		_buff[_count][0] = r;
		_buff[_count][1] = c;
		_buff[_count][2] = tmp;
		_count++;
	}

	public void appendBlock(long r_offset, long c_offset, MatrixBlock inBlk, byte index, OutputCollector<Writable, Writable> out ) 
		throws IOException
	{
		if( inBlk.isInSparseFormat() ) //SPARSE
		{
			Iterator<IJV> iter = inBlk.getSparseBlockIterator();
			while( iter.hasNext() )
			{
				IJV cell = iter.next();
				long tmp = Double.doubleToRawLongBits(cell.getV());
				_buff[_count][0] = r_offset + cell.getI();
				_buff[_count][1] = c_offset + cell.getJ();
				_buff[_count][2] = tmp;
				_count++;
				
				//check and flush if required
				if( _count ==_bufflen )
					flushBuffer(index, out);
			}
		}
		else //DENSE
		{
			//System.out.println("dense merge with ro="+r_offset+", co="+c_offset);
			int rlen = inBlk.getNumRows();
			int clen = inBlk.getNumColumns();
			for( int i=0; i<rlen; i++ )
				for( int j=0; j<clen; j++ )
				{
					double val = inBlk.getValueDenseUnsafe(i, j);
					if( val !=0 )
					{
						long tmp = Double.doubleToRawLongBits(val);
						_buff[_count][0] = r_offset + i;
						_buff[_count][1] = c_offset + j;
						_buff[_count][2] = tmp;
						_count++;
						
						//check and flush if required
						if( _count ==_bufflen )
							flushBuffer(index, out);
					}
				}
		}
	}
	
	public int getSize()
	{
		return _count;
	}
	
	public int getCapacity()
	{
		return _bufflen;
	}

	public void flushBuffer( byte index, OutputCollector<Writable, Writable> out ) 
		throws IOException
	{
		if( _count == 0 )
			return;
		
		//Step 1) sort reblock buffer (blockwise, no in-block sorting!)
		Arrays.sort( _buff, 0 ,_count, new ReblockBufferComparator() );
		
		//Step 2) scan for number of created blocks
		long numBlocks = 0; //number of blocks in buffer
		long cbi = -1, cbj = -1; //current block indexes
		for( int i=0; i<_count; i++ )
		{
			long bi = UtilFunctions.computeBlockIndex(_buff[i][0], _brlen);
			long bj = UtilFunctions.computeBlockIndex(_buff[i][1], _bclen);
			
			//switch to next block
			if( bi != cbi || bj != cbj ) {
				cbi = bi;
				cbj = bj;
				numBlocks++;
			}
		}
		
		//Step 3) decide on intermediate representation (for entire buffer)
		//decision based on binarycell vs binaryblock_ultrasparse (worstcase)
		long blockedSize = 16 * numBlocks + 16 * _count; //<long,long>,#<int,int,double>
		long cellSize = 24 * _count; //#<long,long>,<double>
		boolean blocked = ( blockedSize <= cellSize );
		
		//Step 4) output blocks / binary cell (one-at-a-time)
		TaggedAdaptivePartialBlock outTVal = new TaggedAdaptivePartialBlock();
		AdaptivePartialBlock outVal = new AdaptivePartialBlock();
		MatrixIndexes tmpIx = new MatrixIndexes();
		outTVal.setTag(index);
		outTVal.setBaseObject(outVal); //setup wrapper writables
		if( blocked ) //output binaryblock
		{
			//create intermediate blocks
			boolean sparse = MatrixBlock.evalSparseFormatInMemory(_brlen, _bclen, _count/numBlocks);
			MatrixBlock tmpBlock = new MatrixBlock();
			
			//put values into block and output
			cbi = -1; cbj = -1; //current block indexes
			for( int i=0; i<_count; i++ )
			{
				long bi = UtilFunctions.computeBlockIndex(_buff[i][0], _brlen);
				long bj = UtilFunctions.computeBlockIndex(_buff[i][1], _bclen);
				
				//output block and switch to next index pair
				if( bi != cbi || bj != cbj ) {
					outputBlock(out, tmpIx, outTVal, tmpBlock);
					cbi = bi;
					cbj = bj;
					tmpIx.setIndexes(bi, bj);
					tmpBlock.reset(
						UtilFunctions.computeBlockSize(_rlen, bi, _brlen),
						UtilFunctions.computeBlockSize(_clen, bj, _bclen), sparse);
				}
				
				int ci = UtilFunctions.computeCellInBlock(_buff[i][0], _brlen);
				int cj = UtilFunctions.computeCellInBlock(_buff[i][1], _bclen);
				double tmp = Double.longBitsToDouble(_buff[i][2]);
				tmpBlock.appendValue(ci, cj, tmp); 
			}
			
			//output last block 
			outputBlock(out, tmpIx, outTVal, tmpBlock);
		}
		else //output binarycell
		{
			PartialBlock tmpVal = new PartialBlock();
			outVal.set(tmpVal);
			for( int i=0; i<_count; i++ )
			{
				long bi = UtilFunctions.computeBlockIndex(_buff[i][0], _brlen);
				long bj = UtilFunctions.computeBlockIndex(_buff[i][1], _bclen);
				int ci = UtilFunctions.computeCellInBlock(_buff[i][0], _brlen);
				int cj = UtilFunctions.computeCellInBlock(_buff[i][1], _bclen);
				double tmp = Double.longBitsToDouble(_buff[i][2]);
				tmpIx.setIndexes(bi, bj);
				tmpVal.set(ci, cj, tmp); //in outVal, in outTVal
				out.collect(tmpIx, outTVal);
			}
		}
		
		_count = 0;
	}

	public List<IndexedMatrixValue> flushBufferToBinaryBlocks() 
		throws IOException, DMLRuntimeException
	{
		if( _count == 0 )
			return Collections.emptyList();
		
		//Step 1) sort reblock buffer (blockwise, no in-block sorting!)
		Arrays.sort( _buff, 0 ,_count, new ReblockBufferComparator() );
		
		//Step 2) scan for number of created blocks
		long numBlocks = 0; //number of blocks in buffer
		long cbi = -1, cbj = -1; //current block indexes
		for( int i=0; i<_count; i++ )
		{
			long bi = UtilFunctions.computeBlockIndex(_buff[i][0], _brlen);
			long bj = UtilFunctions.computeBlockIndex(_buff[i][1], _bclen);
			
			//switch to next block
			if( bi != cbi || bj != cbj ) {
				cbi = bi;
				cbj = bj;
				numBlocks++;
			}
		}
		
		//Step 3) output blocks
		ArrayList<IndexedMatrixValue> ret = new ArrayList<>();
		boolean sparse = MatrixBlock.evalSparseFormatInMemory(_brlen, _bclen, _count/numBlocks);
		MatrixIndexes tmpIx = new MatrixIndexes();
		MatrixBlock tmpBlock = new MatrixBlock();
		
		//put values into block and output
		cbi = -1; cbj = -1; //current block indexes
		for( int i=0; i<_count; i++ )
		{
			long bi = UtilFunctions.computeBlockIndex(_buff[i][0], _brlen);
			long bj = UtilFunctions.computeBlockIndex(_buff[i][1], _bclen);
			
			//output block and switch to next index pair
			if( bi != cbi || bj != cbj ) {
				outputBlock(ret, tmpIx, tmpBlock);
				cbi = bi;
				cbj = bj;
				tmpIx = new MatrixIndexes(bi, bj);
				tmpBlock = new MatrixBlock(
					UtilFunctions.computeBlockSize(_rlen, bi, _brlen),
					UtilFunctions.computeBlockSize(_clen, bj, _bclen), sparse);
			}
			
			int ci = UtilFunctions.computeCellInBlock(_buff[i][0], _brlen);
			int cj = UtilFunctions.computeCellInBlock(_buff[i][1], _bclen);
			double tmp = Double.longBitsToDouble(_buff[i][2]);
			tmpBlock.appendValue(ci, cj, tmp); 
		}
		
		//output last block 
		outputBlock(ret, tmpIx, tmpBlock);
		_count = 0;
		return ret;
	}

	private static void outputBlock( OutputCollector<Writable, Writable> out, MatrixIndexes key, TaggedAdaptivePartialBlock value, MatrixBlock block ) 
		throws IOException
	{
		//skip output of unassigned blocks
		if( key.getRowIndex() == -1 || key.getColumnIndex() == -1 )
			return;
		
		//sort sparse rows due to blockwise buffer sort and append  
		if( block.isInSparseFormat() )
			block.sortSparseRows();
		
		//output block
		value.getBaseObject().set(block);
		out.collect(key, value);
	}

	private static void outputBlock( ArrayList<IndexedMatrixValue> out, MatrixIndexes key, MatrixBlock value ) 
		throws IOException, DMLRuntimeException
	{
		//skip output of unassigned blocks
		if( key.getRowIndex() == -1 || key.getColumnIndex() == -1 )
			return;
		
		//sort sparse rows due to blockwise buffer sort and append  
		if( value.isInSparseFormat() )
			value.sortSparseRows();
		
		//ensure correct representation (for in-memory blocks)
		value.examSparsity();
	
		//convert ultra-sparse blocks from MCSR to COO in order to 
		//significantly reduce temporary memory pressure until write 
		if( value.isUltraSparse() )
			value = new MatrixBlock(value, Type.COO, false);
		
		//output block
		out.add(new IndexedMatrixValue(key,value));
	}
	
	/**
	 * Comparator to sort the reblock buffer by block indexes, where we 
	 * compute the block indexes on-the-fly based on the given cell indexes.
	 * 
	 */
	private class ReblockBufferComparator implements Comparator<long[]> 
	{	
		@Override
		public int compare(long[] arg0, long[] arg1) 
		{
			long bi0 = UtilFunctions.computeBlockIndex( arg0[0], _brlen );
			long bj0 = UtilFunctions.computeBlockIndex( arg0[1], _bclen );
			long bi1 = UtilFunctions.computeBlockIndex( arg1[0], _brlen );
			long bj1 = UtilFunctions.computeBlockIndex( arg1[1], _bclen );
			
			return ( bi0 < bi1 || (bi0 == bi1 && bj0 < bj1) ) ? -1 :
                   (( bi0 == bi1 && bj0 == bj1)? 0 : 1);		
		}		
	}
}

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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map.Entry;

import org.apache.hadoop.mapred.Reporter;

import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.io.MatrixWriter;
import org.apache.sysml.runtime.matrix.data.CTableMap;
import org.apache.sysml.runtime.matrix.data.MatrixBlock;
import org.apache.sysml.runtime.matrix.data.MatrixCell;
import org.apache.sysml.runtime.matrix.data.MatrixIndexes;
import org.apache.sysml.runtime.util.LongLongDoubleHashMap.ADoubleEntry;


public class GMRCtableBuffer 
{
	
	//buffer size is tradeoff between preaggregation and efficient hash probes
	//4k entries * ~64byte = 256KB (common L2 cache size)
	public static final int MAX_BUFFER_SIZE = 4096; 
	
	private HashMap<Byte, CTableMap> _mapBuffer = null;
	private HashMap<Byte, MatrixBlock> _blockBuffer = null;
	private CollectMultipleConvertedOutputs _collector = null;

	private byte[] _resultIndexes = null;
	private long[] _resultNonZeros = null;
	private byte[] _resultDimsUnknown = null;
	private long[] _resultMaxRowDims = null;
	private long[] _resultMaxColDims = null;
	
	
	public GMRCtableBuffer( CollectMultipleConvertedOutputs collector, boolean outputDimsKnown )
	{
		if ( outputDimsKnown )
			_blockBuffer = new HashMap<>();
		else
			_mapBuffer = new HashMap<>();
		_collector = collector;
	}

	public void setMetadataReferences(byte[] resultIndexes, long[] resultsNonZeros, byte[] resultDimsUnknown, long[] resultsMaxRowDims, long[] resultsMaxColDims)
	{
		_resultIndexes = resultIndexes;
		_resultNonZeros = resultsNonZeros;
		_resultDimsUnknown = resultDimsUnknown;
		_resultMaxRowDims = resultsMaxRowDims;
		_resultMaxColDims = resultsMaxColDims;
	}

	public int getBufferSize()
	{
		if ( _mapBuffer != null ) {
			int ret = 0;
			for( Entry<Byte, CTableMap> ctable : _mapBuffer.entrySet() )
				ret += ctable.getValue().size();
			return ret;
		}
		else if ( _blockBuffer != null ) {
			int ret = 0;
			for( Entry<Byte, MatrixBlock> ctable: _blockBuffer.entrySet()) {
				ctable.getValue().recomputeNonZeros();
				ret += MatrixBlock.estimateSizeInMemory(
						ctable.getValue().getNumRows(), 
						ctable.getValue().getNumColumns(), 
						((double)ctable.getValue().getNonZeros()/ctable.getValue().getNumRows())*ctable.getValue().getNumColumns());
			}
			return ret;
		}
		else {
			return 0;
		}
	}

	public HashMap<Byte, CTableMap> getMapBuffer()
	{
		return _mapBuffer;
	}
	
	public HashMap<Byte, MatrixBlock> getBlockBuffer() 
	{
		return _blockBuffer;
	}

	public void flushBuffer( Reporter reporter ) 
		throws RuntimeException 
	{
		try
		{
			if ( _mapBuffer != null ) {
				MatrixIndexes key=null;//new MatrixIndexes();
				MatrixCell value=new MatrixCell();
				for(Entry<Byte, CTableMap> ctable: _mapBuffer.entrySet())
				{
					ArrayList<Integer> resultIDs = ReduceBase.getOutputIndexes(ctable.getKey(), _resultIndexes);
					CTableMap resultMap = ctable.getValue();
					
					//maintain result dims and nonzeros
					for(Integer i: resultIDs) {
						_resultNonZeros[i] += resultMap.size();
						if( _resultDimsUnknown[i] == (byte) 1 ) {
							_resultMaxRowDims[i] = Math.max( resultMap.getMaxRow(), _resultMaxRowDims[i]);
							_resultMaxColDims[i] = Math.max( resultMap.getMaxColumn(), _resultMaxColDims[i]);
						}
					}
					
					//output result data 
					Iterator<ADoubleEntry> iter = resultMap.getIterator();
					while( iter.hasNext() ) {
						ADoubleEntry e = iter.next();
						key = new MatrixIndexes(e.getKey1(), e.getKey2());
						value.setValue(e.value);
						for(Integer i: resultIDs)
							_collector.collectOutput(key, value, i, reporter);
					}
				}
			}
			else if ( _blockBuffer != null ) {
				MatrixIndexes key=new MatrixIndexes(1,1);
				//DataConverter.writeBinaryBlockMatrixToHDFS(path, job, mat, mc.get_rows(), mc.get_cols(), mc.get_rows_per_block(), mc.get_cols_per_block(), replication);
				for(Entry<Byte, MatrixBlock> ctable: _blockBuffer.entrySet())
				{
					ArrayList<Integer> resultIDs=ReduceBase.getOutputIndexes(ctable.getKey(), _resultIndexes);
					MatrixBlock outBlock = ctable.getValue();
					outBlock.recomputeNonZeros();
					
					// TODO: change hard coding of 1000
					int brlen = 1000, bclen = 1000;
					int rlen = outBlock.getNumRows();
					int clen = outBlock.getNumColumns();
					
					// final output matrix is smaller than a single block
					if(rlen <= brlen && clen <= brlen ) {
						key = new MatrixIndexes(1,1);
						for(Integer i: resultIDs)
						{
							_collector.collectOutput(key, outBlock, i, reporter);
							_resultNonZeros[i]+= outBlock.getNonZeros();
						}
					}
					
					else {
						//Following code is similar to that in DataConverter.DataConverter.writeBinaryBlockMatrixToHDFS
						//initialize blocks for reuse (at most 4 different blocks required)
						MatrixBlock[] blocks = MatrixWriter.createMatrixBlocksForReuse(rlen, clen, brlen, bclen, true, outBlock.getNonZeros());  
						
						//create and write subblocks of matrix
						for(int blockRow = 0; blockRow < (int)Math.ceil(rlen/(double)brlen); blockRow++) {
							for(int blockCol = 0; blockCol < (int)Math.ceil(clen/(double)bclen); blockCol++)
							{
								int maxRow = (blockRow*brlen + brlen < rlen) ? brlen : rlen - blockRow*brlen;
								int maxCol = (blockCol*bclen + bclen < clen) ? bclen : clen - blockCol*bclen;
						
								int row_offset = blockRow*brlen;
								int col_offset = blockCol*bclen;
								
								//get reuse matrix block
								MatrixBlock block = MatrixWriter.getMatrixBlockForReuse(blocks, maxRow, maxCol, brlen, bclen);
			
								//copy submatrix to block
								outBlock.slice( row_offset, row_offset+maxRow-1, 
														  col_offset, col_offset+maxCol-1, block );
								
								// TODO: skip empty "block"
								
								//append block to sequence file
								key.setIndexes(blockRow+1, blockCol+1);
								for(Integer i: resultIDs)
								{
									_collector.collectOutput(key, block, i, reporter);
									_resultNonZeros[i]+= block.getNonZeros();
								}
								
								//reset block for later reuse
								block.reset();
							}
						}
					}
				}
			}
			else {
				throw new DMLRuntimeException("Unexpected.. both ctable buffers are empty.");
			}
		}
		catch(Exception ex)
		{
			throw new RuntimeException("Failed to flush ctable buffer.", ex);
		}
		//remove existing partial ctables
		if (_mapBuffer != null ) 
			_mapBuffer.clear();
		else 
			_blockBuffer.clear();
	}
}

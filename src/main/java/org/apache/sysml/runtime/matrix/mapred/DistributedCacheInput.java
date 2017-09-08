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

import java.io.File;
import java.util.ArrayList;

import org.apache.hadoop.fs.Path;

import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.controlprogram.ParForProgramBlock.PDataPartitionFormat;
import org.apache.sysml.runtime.io.MatrixReaderFactory;
import org.apache.sysml.runtime.io.ReaderBinaryBlock;
import org.apache.sysml.runtime.matrix.data.InputInfo;
import org.apache.sysml.runtime.matrix.data.MatrixBlock;
import org.apache.sysml.runtime.matrix.data.MatrixIndexes;
import org.apache.sysml.runtime.util.DataConverter;

public class DistributedCacheInput 
{	
	
	//internal partitioning parameter (threshold and partition size) 
	public static final long PARTITION_SIZE = 4000000; //32MB
	//public static final String PARTITION_SUFFIX = "_dp";
	
	//meta data of cache input
	private Path _localFilePath = null;
	private long _rlen = -1;
	private long _clen = -1;
	private int _brlen = -1;
	private int _bclen = -1;
	private PDataPartitionFormat _pformat = null;
	
	//data cached input
	private IndexedMatrixValue[][] dataBlocks = null;
	
	
	public DistributedCacheInput(Path p, long rows, long cols, int brlen, int bclen, PDataPartitionFormat pformat) 
	{
		_localFilePath = p;
		_rlen  = rows;
		_clen  = cols;
		_brlen = brlen;
		_bclen = bclen;
		_pformat = pformat;
	}

	public long getNumRows() {
		return _rlen;
	}
	
	public long getNumCols() {
		return _clen;
	}
	
	public int getNumRowsPerBlock(){
		return _brlen;
	}
	
	public int getNumColsPerBlock(){
		return _bclen;
	}

	public void reset() 
	{
		_localFilePath = null;
		_rlen  = -1;
		_clen  = -1;
		_brlen = -1;
		_bclen = -1;
		_pformat = null;
	}

	public IndexedMatrixValue getDataBlock(int rowBlockIndex, int colBlockIndex)
		throws DMLRuntimeException 
	{
		//probe missing block (read on-demand)
		if( dataBlocks==null || dataBlocks[rowBlockIndex-1][colBlockIndex-1]==null )
			readDataBlocks( rowBlockIndex, colBlockIndex );
		
		//return read or existing block
		return dataBlocks[rowBlockIndex-1][colBlockIndex-1];
	}

	public double[] getRowVectorArray() 
		throws DMLRuntimeException
	{
		double[] ret = new double[(int)_clen];
		
		for( int j=0; j<_clen; j+=_bclen ) {
			MatrixBlock mb = (MatrixBlock) getDataBlock(1, (int)Math.ceil((double)(j+1)/_bclen)).getValue(); 
			double[] mbtmp = DataConverter.convertToDoubleVector(mb, false);
			System.arraycopy(mbtmp, 0, ret, j, mbtmp.length);
		}
		
		return ret;
	}

	public double[] getColumnVectorArray() 
		throws DMLRuntimeException
	{
		double[] ret = new double[(int)_rlen];
		
		for( int j=0; j<_rlen; j+=_brlen ) {
			MatrixBlock mb = (MatrixBlock) getDataBlock((int)Math.ceil((double)(j+1)/_brlen),1).getValue(); 
			double[] mbtmp = DataConverter.convertToDoubleVector(mb, false);
			System.arraycopy(mbtmp, 0, ret, j, mbtmp.length);
		}
		
		return ret;
	}

	private void readDataBlocks( int rowBlockIndex, int colBlockIndex )
		throws DMLRuntimeException 
	{
		//get filename for rowblock/colblock
		String fname = _localFilePath.toString();
		if( isPartitioned() ) 
			fname = getPartitionFileName(rowBlockIndex, colBlockIndex);
			
		//read matrix partition (or entire vector)
		try 
		{		
			ReaderBinaryBlock reader = (ReaderBinaryBlock) MatrixReaderFactory.createMatrixReader(InputInfo.BinaryBlockInputInfo);
			reader.setLocalFS( !MRBaseForCommonInstructions.isJobLocal );
			ArrayList<IndexedMatrixValue> tmp = reader.readIndexedMatrixBlocksFromHDFS(fname, _rlen, _clen, _brlen, _bclen);
			
			int rowBlocks = (int) Math.ceil(_rlen / (double) _brlen);
			int colBlocks = (int) Math.ceil(_clen / (double) _bclen);

			if( dataBlocks==null )
				dataBlocks = new IndexedMatrixValue[rowBlocks][colBlocks];

			for (IndexedMatrixValue val : tmp) {
				MatrixIndexes idx = val.getIndexes();
				dataBlocks[(int) idx.getRowIndex() - 1][(int) idx.getColumnIndex() - 1] = val;
			}
		} 
		catch (Exception ex) {
			throw new DMLRuntimeException(ex);
		} 
	}

	private boolean isPartitioned()
	{
		return (_pformat != PDataPartitionFormat.NONE);
	}

	private String getPartitionFileName( int rowBlockIndex, int colBlockIndex  ) 
		throws DMLRuntimeException
	{
		long partition = -1;
		switch( _pformat )
		{
			case ROW_BLOCK_WISE_N:
			{
				long numRowBlocks = (long)Math.ceil(((double)PARTITION_SIZE)/_clen/_brlen); 
				partition = (rowBlockIndex-1)/numRowBlocks + 1;	
				break;
			}
			case COLUMN_BLOCK_WISE_N:
			{
				long numColBlocks = (long)Math.ceil(((double)PARTITION_SIZE)/_rlen/_bclen); 
				partition = (colBlockIndex-1)/numColBlocks + 1;
				break;
			}
			
			default: 
				throw new DMLRuntimeException("Unsupported partition format for distributed cache input: "+_pformat);
		}
		
		return _localFilePath.toString() + File.separator + partition;
	}
}

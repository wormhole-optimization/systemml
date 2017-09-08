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

package org.apache.sysml.runtime.matrix.data;

import java.util.Iterator;

import org.apache.sysml.runtime.util.LongLongDoubleHashMap;
import org.apache.sysml.runtime.util.LongLongDoubleHashMap.LLDoubleEntry;

/**
 * Ctable map is an abstraction for the hashmap used for ctable's hash group-by
 * because this structure is passed through various interfaces. This makes it 
 * easier to (1) exchange the underlying data structure and (2) maintain statistics 
 * like max row/column in order to prevent scans during data conversion.
 * 
 */
public class CTableMap 
{
	private LongLongDoubleHashMap _map = null;
	private long _maxRow = -1;
	private long _maxCol = -1;
	
	public CTableMap() {
		_map = new LongLongDoubleHashMap();
		_maxRow = -1;
		_maxCol = -1;
	}

	public int size() {
		return _map.size();
	}
	
	public Iterator<LLDoubleEntry> getIterator() {
		return _map.getIterator();
	}

	public long getMaxRow() {
		return _maxRow;
	}

	public long getMaxColumn() {
		return _maxCol;
	}

	public void aggregate(long row, long col, double w) 
	{
		//hash group-by for core ctable computation
		_map.addValue(row, col, w);
		
		//maintain internal summaries 
		_maxRow = Math.max(_maxRow, row);
		_maxCol = Math.max(_maxCol, col);
	}

	public MatrixBlock toMatrixBlock(int rlen, int clen)
	{
		//allocate new matrix block
		int nnz = _map.size();
		boolean sparse = MatrixBlock.evalSparseFormatInMemory(rlen, clen, nnz); 		
		MatrixBlock mb = new MatrixBlock(rlen, clen, sparse, nnz);
		
		// copy map values into new matrix block
		if( sparse ) //SPARSE <- cells
		{
			//append cells to sparse target (prevent shifting)
			Iterator<LLDoubleEntry> iter2 = _map.getIterator();
			while( iter2.hasNext() ) {
				LLDoubleEntry e = iter2.next();
				double value = e.value;
				int rix = (int)e.key1;
				int cix = (int)e.key2;
				if( value != 0 && rix<=rlen && cix<=clen )
					mb.appendValue( rix-1, cix-1, value );
			}
			
			//sort sparse target representation
			mb.sortSparseRows();
		}
		else  //DENSE <- cells
		{
			//directly insert cells into dense target 
			Iterator<LLDoubleEntry> iter = _map.getIterator();
			while( iter.hasNext() ) {
				LLDoubleEntry e = iter.next();
				double value = e.value;
				int rix = (int)e.key1;
				int cix = (int)e.key2;
				if( value != 0 && rix<=rlen && cix<=clen )
					mb.quickSetValue( rix-1, cix-1, value );
			}
		}
		
		return mb;
	}
}

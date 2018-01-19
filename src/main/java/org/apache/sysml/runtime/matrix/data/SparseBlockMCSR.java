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

/**
 * SparseBlock implementation that realizes a 'modified compressed sparse row'
 * representation, where each compressed row is stored as a separate SparseRow
 * object which provides flexibility for unsorted row appends without the need 
 * for global reshifting of values/indexes but it incurs additional memory 
 * overhead per row for object/array headers per row which also slows down
 * memory-bound operations due to higher memory bandwidth requirements.
 * 
 */
public class SparseBlockMCSR extends SparseBlock
{
	private static final long serialVersionUID = -4743624499258436199L;
	
	private SparseRow[] _rows = null;
	
	/**
	 * Copy constructor sparse block abstraction. 
	 * 
	 * @param sblock sparse block to copy
	 */
	public SparseBlockMCSR(SparseBlock sblock)
	{
		//special case SparseBlockMCSR
		if( sblock instanceof SparseBlockMCSR ) { 
			SparseRow[] orows = ((SparseBlockMCSR)sblock)._rows;
			_rows = new SparseRow[orows.length];
			for( int i=0; i<_rows.length; i++ )
				_rows[i] = new SparseRowVector(orows[i]);
		}
		//general case SparseBlock
		else { 
			_rows = new SparseRow[sblock.numRows()];
			for( int i=0; i<_rows.length; i++ ) {
				if( !sblock.isEmpty(i) ) {
					int apos = sblock.pos(i);
					int alen = sblock.size(i);
					_rows[i] = new SparseRowVector(alen);
					((SparseRowVector)_rows[i]).setSize(alen);
					System.arraycopy(sblock.indexes(i), apos, _rows[i].indexes(), 0, alen);
					System.arraycopy(sblock.values(i), apos, _rows[i].values(), 0, alen);
				}
			}
		}
	}
	
	/**
	 * Copy constructor old sparse row representation. 
	 * 
	 * @param rows array of sparse rows
	 * @param deep if true, deep copy
	 */
	public SparseBlockMCSR(SparseRow[] rows, boolean deep) {
		if( deep ) {
			_rows = new SparseRow[rows.length];
			for( int i=0; i<_rows.length; i++ ) {
				_rows[i] = (rows[i].size()==1) ? new SparseRowScalar(
					rows[i].indexes()[0], rows[i].values()[0]) : 
					new SparseRowVector(rows[i]);
			}
		}
		else {
			_rows = rows;
		}
	}
	
	public SparseBlockMCSR(int rlen, int clen) {
		_rows = new SparseRow[rlen];
	}
	
	/**
	 * Get the estimated in-memory size of the sparse block in MCSR 
	 * with the given dimensions w/o accounting for overallocation. 
	 * 
	 * @param nrows number of rows
	 * @param ncols number of columns
	 * @param sparsity sparsity ratio
	 * @return memory estimate
	 */
	public static long estimateMemory(long nrows, long ncols, double sparsity) {
		double cnnz = Math.max(SparseRowVector.initialCapacity, Math.ceil(sparsity*ncols));
		double rlen = Math.min(nrows, Math.ceil(sparsity*nrows*ncols));
		
		//Each sparse row has a fixed overhead of 8B (reference) + 32B (object) +
		//12B (3 int members), 32B (overhead int array), 32B (overhead double array),
		//Each non-zero value requires 12B for the column-index/value pair.
		//Overheads for arrays, objects, and references refer to 64bit JVMs
		//If nnz < than rows we have only also empty rows.
		double size = 16;                 //object
		size += rlen * (116 + cnnz * 12); //sparse rows
		size += 32 + nrows * 8d;          //references
		
		// robustness for long overflows
		return (long) Math.min(size, Long.MAX_VALUE);
	}

	///////////////////
	//SparseBlock implementation

	@Override
	public void allocate(int r) {
		if( !isAllocated(r) )
			_rows[r] = new SparseRowVector();
	}
	
	@Override
	public void allocate(int r, int nnz) {
		if( !isAllocated(r) )
			_rows[r] = (nnz == 1) ? new SparseRowScalar() :
				new SparseRowVector(nnz);
	}
	
	@Override
	public void allocate(int r, int ennz, int maxnnz) {
		if( !isAllocated(r) )
			_rows[r] = (ennz == 1) ? new SparseRowScalar() :
				new SparseRowVector(ennz, maxnnz);
	}
	
	@Override
	public int numRows() {
		return _rows.length;
	}

	@Override
	public boolean isThreadSafe() {
		return true;
	}
	
	@Override
	public boolean isContiguous() {
		return false;
	}
	
	@Override
	public boolean isAllocated(int r) {
		return (_rows[r] != null);
	}
	
	@Override 
	public void reset() {
		for( SparseRow row : _rows )
			if( row != null )
				row.reset(row.size(), Integer.MAX_VALUE);
	}
	
	@Override 
	public void reset(int ennz, int maxnnz) {
		for( SparseRow row : _rows )
			if( row != null )
				row.reset(ennz, maxnnz);
	}
	
	@Override 
	public void reset(int r, int ennz, int maxnnz) {
		if( isAllocated(r) )
			_rows[r].reset(ennz, maxnnz);
	}
	
	@Override
	public long size() {
		//recompute non-zeros to avoid redundant maintenance
		long nnz = 0;
		for( SparseRow row : _rows )
			if( row != null ) 
				nnz += row.size();
		return nnz;
	}

	@Override
	public int size(int r) {
		//prior check with isEmpty(r) expected
		return isAllocated(r) ? _rows[r].size() : 0;
	}
	
	@Override
	public long size(int rl, int ru) {
		int ret = 0;
		for( int i=rl; i<ru; i++ )
			ret += isAllocated(i) ? _rows[i].size() : 0;
		return ret;
	}
	
	@Override
	public long size(int rl, int ru, int cl, int cu) {
		long nnz = 0;
		for(int i=rl; i<ru; i++)
			if( !isEmpty(i) ) {
				int start = posFIndexGTE(i, cl);
				int end = posFIndexGTE(i, cu);
				nnz += (start!=-1) ? (end-start) : 0;
			}
		return nnz;
	}

	@Override
	public boolean isEmpty(int r) {
		return (!isAllocated(r) || _rows[r].isEmpty());
	}
	
	@Override
	public int[] indexes(int r) {
		//prior check with isEmpty(r) expected
		return _rows[r].indexes();
	}

	@Override
	public double[] values(int r) {
		//prior check with isEmpty(r) expected
		return _rows[r].values();
	}

	@Override
	public int pos(int r) {
		//arrays per row (always start 0)
		return 0;
	}

	@Override
	public boolean set(int r, int c, double v) {
		if( !isAllocated(r) )
			_rows[r] = new SparseRowScalar();
		else if( _rows[r] instanceof SparseRowScalar && !_rows[r].isEmpty())
			_rows[r] = new SparseRowVector(_rows[r]);
		return _rows[r].set(c, v);
	}

	@Override
	public void set(int r, SparseRow row, boolean deep) {
		//copy values into existing row to avoid allocation
		if( isAllocated(r) && _rows[r] instanceof SparseRowVector
			&& ((SparseRowVector)_rows[r]).capacity() >= row.size() && deep )
			((SparseRowVector)_rows[r]).copy(row);
		//set new sparse row (incl allocation if required)
		else 
			_rows[r] = (deep && row != null) ?
				new SparseRowVector(row) : row;
	}
	
	@Override
	public void append(int r, int c, double v) {
		if( !isAllocated(r) )
			_rows[r] = new SparseRowScalar();
		else if( _rows[r] instanceof SparseRowScalar && !_rows[r].isEmpty() )
			_rows[r] = new SparseRowVector(_rows[r]);
		_rows[r].append(c, v);
	}

	@Override
	public void setIndexRange(int r, int cl, int cu, double[] v, int vix, int len) {
		if( !isAllocated(r) )
			_rows[r] = new SparseRowVector();
		else if( _rows[r] instanceof SparseRowScalar )
			_rows[r] = new SparseRowVector(_rows[r]);
		//different sparse row semantics: upper bound inclusive
		((SparseRowVector)_rows[r]).setIndexRange(cl, cu-1, v, vix, len);
	}

	@Override
	public void deleteIndexRange(int r, int cl, int cu) {
		//prior check with isEmpty(r) expected
		//different sparse row semantics: upper bound inclusive
		if( _rows[r] instanceof SparseRowScalar )
			_rows[r] = new SparseRowVector(_rows[r]);
		((SparseRowVector)_rows[r]).deleteIndexRange(cl, cu-1);
	}

	@Override
	public void sort() {
		for( SparseRow row : _rows )
			if( row != null && !row.isEmpty() )
				row.sort();
	}

	@Override
	public void sort(int r) {
		//prior check with isEmpty(r) expected
		_rows[r].sort();
	}

	@Override
	public double get(int r, int c) {
		if( !isAllocated(r) )
			return 0;
		return _rows[r].get(c); 
	}
	
	@Override
	public SparseRow get(int r) {
		return _rows[r]; 
	}

	@Override
	public int posFIndexLTE(int r, int c) {
		//prior check with isEmpty(r) expected
		if( _rows[r] instanceof SparseRowScalar )
			_rows[r] = new SparseRowVector(_rows[r]);
		return ((SparseRowVector)_rows[r]).searchIndexesFirstLTE(c);
	}

	@Override
	public int posFIndexGTE(int r, int c) {
		//prior check with isEmpty(r) expected
		if( _rows[r] instanceof SparseRowScalar )
			_rows[r] = new SparseRowVector(_rows[r]);
		return ((SparseRowVector)_rows[r]).searchIndexesFirstGTE(c);
	}

	@Override
	public int posFIndexGT(int r, int c) {
		//prior check with isEmpty(r) expected
		if( _rows[r] instanceof SparseRowScalar )
			_rows[r] = new SparseRowVector(_rows[r]);
		return ((SparseRowVector)_rows[r]).searchIndexesFirstGT(c);
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("SparseBlockMCSR: rlen=");
		sb.append(numRows());
		sb.append(", nnz=");
		sb.append(size());
		sb.append("\n");
		for( int i=0; i<numRows(); i++ ) {
			sb.append("row +");
			sb.append(i);
			sb.append(": ");
			sb.append(_rows[i]);
			sb.append("\n");
		}
		
		return sb.toString();
	}
	
	/**
	 * Helper function for MCSR -&gt; {COO, CSR}
	 * @return the underlying array of {@link SparseRow}
	 */
	public SparseRow[] getRows() {
		return _rows;
	}
}

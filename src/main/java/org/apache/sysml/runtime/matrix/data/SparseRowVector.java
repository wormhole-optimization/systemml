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

import java.io.Serializable;
import java.util.Arrays;

import org.apache.sysml.runtime.util.SortUtils;

public final class SparseRowVector extends SparseRow implements Serializable 
{
	private static final long serialVersionUID = 2971077474424464992L;

	//initial capacity of any created sparse row
	//WARNING: be aware that this affects the core memory estimates (incl. implicit assumptions)! 
	public static final int initialCapacity = 4;
	
	private int estimatedNzs = initialCapacity;
	private int maxNzs = Integer.MAX_VALUE;
	private int size = 0;
	private double[] values = null;
	private int[] indexes = null;
	
	public SparseRowVector() {
		this(initialCapacity);
	}
	
	public SparseRowVector(int capacity) {
		estimatedNzs = capacity;
		values = new double[capacity];
		indexes = new int[capacity];
	}
	
	public SparseRowVector(int estnnz, int maxnnz) {
		if( estnnz > initialCapacity )
			estimatedNzs = estnnz;
		maxNzs = maxnnz;
		int capacity = ((estnnz<initialCapacity && estnnz>0) ? 
				         estnnz : initialCapacity);
		values = new double[capacity];
		indexes = new int[capacity];
	}
	
	public SparseRowVector(SparseRow that) {
		size = that.size();
		int cap = Math.max(initialCapacity, that.size());
		
		//allocate arrays and copy new values
		values = Arrays.copyOf(that.values(), cap);
		indexes = Arrays.copyOf(that.indexes(), cap);
	}

	@Override
	public int size() {
		return size;
	}
	
	public void setSize(int newsize) {
		size = newsize;
	}
	
	@Override
	public boolean isEmpty() {
		return (size == 0);
	}
	
	@Override
	public double[] values() {
		return values;
	}
	
	@Override
	public int[] indexes() {
		return indexes;
	}
	
	public void setValues(double[] d) {
		values = d;
	}
	
	public void setIndexes(int[] i) {
		indexes = i;
	}
	
	public int capacity() {
		return values.length;
	}

	public void copy(SparseRow that)
	{
		//note: no recap (if required) + copy, in order to prevent unnecessary copy of old values
		//in case we have to reallocate the arrays
		
		int thatSize = that.size();
		if( values.length < thatSize ) {
			//reallocate arrays and copy new values
			values = Arrays.copyOf(that.values(), thatSize);
			indexes = Arrays.copyOf(that.indexes(), thatSize);
		}
		else {
			//copy new values
			System.arraycopy(that.values(), 0, values, 0, thatSize);
			System.arraycopy(that.indexes(), 0, indexes, 0, thatSize);	
		}
		size = thatSize;
	}

	@Override
	public void reset(int estnns, int maxnns) {
		estimatedNzs = estnns;
		maxNzs = maxnns;
		size = 0;
	}

	private void recap(int newCap) {
		if( newCap<=values.length )
			return;
		
		//reallocate arrays and copy old values
		values = Arrays.copyOf(values, newCap);
		indexes = Arrays.copyOf(indexes, newCap);
	}
	
	/**
	 * Heuristic for resizing:
	 *   doubling before capacity reaches estimated nonzeros, then 1.1x after that for default behavior: always 1.1x
	 *   (both with exponential size increase for log N steps of reallocation and shifting)
	 * 
	 * @return new capacity for resizing
	 */
	private int newCapacity() {
		return (int) ((values.length < estimatedNzs) ?
			Math.min(estimatedNzs, values.length*SparseBlock.RESIZE_FACTOR1) :
			Math.min(maxNzs, Math.ceil(values.length*SparseBlock.RESIZE_FACTOR2)));
	}

	@Override
	public boolean set(int col, double v) {
		//search for existing col index
		int index = Arrays.binarySearch(indexes, 0, size, col);
		if( index >= 0 ) {
			//delete/overwrite existing value (on value delete, we shift 
			//left for (1) correct nnz maintenance, and (2) smaller size)
			if( v == 0 ) {
				shiftLeftAndDelete(index);
				return true; // nnz--
			}
			else { 	
				values[index] = v;
				return false;
			} 
		}

		//early abort on zero (if no overwrite)
		if( v==0.0 )
			return false;
		
		//insert new index-value pair
		index = Math.abs( index+1 );
		if( size==values.length )
			resizeAndInsert(index, col, v);
		else
			shiftRightAndInsert(index, col, v);
		return true; // nnz++
	}

	@Override
	public void append(int col, double v) {
		//early abort on zero 
		if( v==0.0 )
			return;
		
		//resize if required
		if( size==values.length )
			recap(newCapacity());
		
		//append value at end
		values[size] = v;
		indexes[size] = col;
		size++;
	}

	@Override
	public double get(int col) {
		//search for existing col index
		int index = Arrays.binarySearch(indexes, 0, size, col);		
		if( index >= 0 )
			return values[index];
		else
			return 0;
	}

	public int searchIndexesFirstLTE(int col)
	{
		//search for existing col index
		int index = Arrays.binarySearch(indexes, 0, size, col);
		if( index >= 0  ) {
			if( index < size )
				return index;
			else 
				return -1;
		}
		
		//search lt col index (see binary search)
		index = Math.abs( index+1 );
		if( index-1 < size )
			return index-1;
		else 
			return -1;
	}

	public int searchIndexesFirstGTE(int col)
	{
		//search for existing col index
		int index = Arrays.binarySearch(indexes, 0, size, col);
		if( index >= 0  ) {
			if( index < size )
				return index;
			else 
				return -1;
		}
		
		//search gt col index (see binary search)
		index = Math.abs( index+1 );
		if( index < size )
			return index;
		else 
			return -1;
	}

	public int searchIndexesFirstGT(int col)
	{
		//search for existing col index
		int index = Arrays.binarySearch(indexes, 0, size, col);
		if( index >= 0  ) {
			if( index+1 < size )
				return index+1;
			else 
				return -1;
		}
		
		//search gt col index (see binary search)
		index = Math.abs( index+1 );
		if( index < size )
			return index;
		else 
			return -1;
	}

	public void deleteIndexRange(int lowerCol, int upperCol)
	{
		int start = searchIndexesFirstGTE(lowerCol);
		if( start < 0 ) //nothing to delete 
			return;
		
		int end = searchIndexesFirstGT(upperCol);
		if( end < 0 ) //delete all remaining
			end = size;
		
		//overlapping array copy (shift rhs values left)
		System.arraycopy(values, end, values, start, size-end);
		System.arraycopy(indexes, end, indexes, start, size-end);
		size -= (end-start);
	}
	
	/**
	 * Inserts a dense vector into a column range; calling this methods helps to
	 * avoid repeated shifting of remaining values/indexes for every set value. 
	 * 
	 * @param lowerCol lower column index
	 * @param upperCol upper column index
	 * @param v dense vector
	 * @param vix ?
	 * @param len ?
	 */
	public void setIndexRange(int lowerCol, int upperCol, double[] v, int vix, int len)
	{
		int start = searchIndexesFirstGTE(lowerCol);
		if( start < 0 ) { //nothing to delete/shift
			for( int i=vix; i<vix+len; i++ )
				append(lowerCol+i-vix, v[i]);
			return;
		}
		
		int end = searchIndexesFirstGT(upperCol);
		if( end < 0 ) { //delete all remaining
			size = start;
			for( int i=vix; i<vix+len; i++ )
				append(lowerCol+i-vix, v[i]);
			return;
		}
		
		//determine input nnz
		int lnnz = 0;
		for( int i=vix; i<vix+len; i++ )
			lnnz += ( v[i] != 0 ) ? 1 : 0;
		
		//prepare free space (allocate and shift)
		int lsize = size+lnnz-(end-start);
		if( values.length < lsize )
			recap(lsize);
		shiftRightByN(end, lnnz-(end-start));
		
		//insert values
		for( int i=vix, pos=start; i<vix+len; i++ )
			if( v[i] != 0 ) {
				values[ pos ] = v[i];
				indexes[ pos ] = lowerCol+i-vix;
				pos++;
			}
	}

	private void resizeAndInsert(int index, int col, double v) {
		//allocate new arrays
		int newCap = newCapacity();
		double[] oldvalues = values;
		int[] oldindexes = indexes;
		values = new double[newCap];
		indexes = new int[newCap];
		
		//copy lhs values to new array
		System.arraycopy(oldvalues, 0, values, 0, index);
		System.arraycopy(oldindexes, 0, indexes, 0, index);
		
		//insert new value
		indexes[index] = col;
		values[index] = v;
		
		//copy rhs values to new array
		System.arraycopy(oldvalues, index, values, index+1, size-index);
		System.arraycopy(oldindexes, index, indexes, index+1, size-index);
		size++;
	}

	private void shiftRightAndInsert(int index, int col, double v) {
		//overlapping array copy (shift rhs values right by 1)
		System.arraycopy(values, index, values, index+1, size-index);
		System.arraycopy(indexes, index, indexes, index+1, size-index);

		//insert new value
		values[index] = v;
		indexes[index] = col;
		size++;
	}

	private void shiftRightByN(int index, int n) {
		//overlapping array copy (shift rhs values right by 1)
		System.arraycopy(values, index, values, index+n, size-index);
		System.arraycopy(indexes, index, indexes, index+n, size-index);
		size += n;
	}

	private void shiftLeftAndDelete(int index) {
		//overlapping array copy (shift rhs values left by 1)
		System.arraycopy(values, index+1, values, index, size-index-1);
		System.arraycopy(indexes, index+1, indexes, index, size-index-1);
		size--;
	}
	
	@Override
	public void sort() {
		if( size<=100 || !SortUtils.isSorted(0, size, indexes) )
			SortUtils.sortByIndex(0, size, indexes, values);
	}
	
	@Override
	public void compact() {
		int nnz = 0;
		for( int i=0; i<size; i++ ) 
			if( values[i] != 0 ){
				values[nnz] = values[i];
				indexes[nnz] = indexes[i];
				nnz++;
			}
		size = nnz; //adjust row size
	}
}

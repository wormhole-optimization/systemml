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

package org.apache.sysml.runtime.util;

import java.util.Iterator;

/**
 * This native long long - double hashmap is specifically designed for
 * ctable operations which only require addvalue - extract semantics.
 * In contrast to a default hashmap the native representation allows us
 * to be more memory-efficient which is important for large maps in order
 * to keep data in the caches and prevent high-latency random memory access. 
 * 
 */
public class LongLongDoubleHashMap 
{
	private static final int INIT_CAPACITY = 8;
	private static final int RESIZE_FACTOR = 2;
	private static final float LOAD_FACTOR = 0.75f;

	private LLDoubleEntry[] data = null;
	private int size = -1;
	
	public LongLongDoubleHashMap()
	{
		data = new LLDoubleEntry[INIT_CAPACITY];
		size = 0;
	}

	public int size() {
		return size;
	}

	public void addValue(long key1, long key2, double value)
	{
		//compute entry index position
		int hash = hash(key1, key2);
		int ix = indexFor(hash, data.length);

		//find existing entry and add value
		for( LLDoubleEntry e = data[ix]; e!=null; e = e.next ) {
			if( e.key1==key1 && e.key2==key2 ) {
				e.value += value;
				return; //no need to append or resize
			}
		}
		
		//add non-existing entry (constant time)
		LLDoubleEntry enew = new LLDoubleEntry(key1, key2, value);
		enew.next = data[ix]; //colliding entries / null
		data[ix] = enew;
		size++;
		
		//resize if necessary
		if( size >= LOAD_FACTOR*data.length )
			resize();
	}

	public Iterator<LLDoubleEntry> getIterator() {
		return new LLDoubleEntryIterator();
	}

	private void resize() {
		//check for integer overflow on resize
		if( data.length > Integer.MAX_VALUE/RESIZE_FACTOR )
			return;
		
		//resize data array and copy existing contents
		LLDoubleEntry[] olddata = data;
		data = new LLDoubleEntry[data.length*RESIZE_FACTOR];
		size = 0;
		
		//rehash all entries
		for( LLDoubleEntry e : olddata ) {
			if( e != null ) {
				while( e.next!=null ) {
					addValue(e.key1, e.key2, e.value);
					e = e.next;
				}
				addValue(e.key1, e.key2, e.value);	
			}
		}
	}

	private static int hash(long key1, long key2) {
		int h = UtilFunctions.longHashCode(key1, key2);
		
		// This function ensures that hashCodes that differ only by
		// constant multiples at each bit position have a bounded
		// number of collisions (approximately 8 at default load factor).
		h ^= (h >>> 20) ^ (h >>> 12);
		return h ^ (h >>> 7) ^ (h >>> 4);
	}

	private static int indexFor(int h, int length) {
		return h & (length-1);
	}

	public class LLDoubleEntry {
		public long key1 = Long.MAX_VALUE;
		public long key2 = Long.MAX_VALUE;
		public double value = Double.MAX_VALUE;
		public LLDoubleEntry next = null;
		
		public LLDoubleEntry(long k1, long k2, double val) {
			key1 = k1;
			key2 = k2;
			value = val;
			next = null;
		}
	}
	
	private class LLDoubleEntryIterator implements Iterator<LLDoubleEntry> {
		private LLDoubleEntry _curr;
		private int _currPos;
		
		public LLDoubleEntryIterator() {
			_curr = null;
			_currPos = -1;
			findNext();
		}
		
		@Override
		public boolean hasNext() {
			return (_curr != null);
		}

		@Override
		public LLDoubleEntry next() {
			LLDoubleEntry ret = _curr;
			findNext();
			return ret;
		}
		
		private void findNext() {
			if( _curr != null && _curr.next != null ) {
				_curr = _curr.next;
				return;
			}
			_currPos++;
			while( _currPos < data.length  ) {
				_curr = data[_currPos];
				if( _curr != null ) 
					return;
				_currPos++;
			}
			_curr = null;
		}
	}
}

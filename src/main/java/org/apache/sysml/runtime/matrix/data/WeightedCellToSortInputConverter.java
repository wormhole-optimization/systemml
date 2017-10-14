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

import org.apache.hadoop.io.DoubleWritable;
import org.apache.hadoop.io.IntWritable;

public class WeightedCellToSortInputConverter implements 
Converter<MatrixIndexes, WeightedCell, DoubleWritable, IntWritable>
{
	private DoubleWritable outKey=new DoubleWritable();
	private IntWritable outValue=new IntWritable();
	private Pair<DoubleWritable, IntWritable> pair=new Pair<>(outKey, outValue);
	private boolean hasValue=false;
	@Override
	public void convert(MatrixIndexes k1, WeightedCell v1) {
		outKey.set(v1.getValue());
		outValue.set((int)v1.getWeight());
		hasValue=true;
	}

	@Override
	public boolean hasNext() {
		return hasValue;
	}

	@Override
	public Pair<DoubleWritable, IntWritable> next() {
		if(!hasValue)
			return null;
		
		hasValue=false;
		return pair;
	}

	@Override
	public void setBlockSize(int rl, int cl) {
		//DO nothing
	}

}

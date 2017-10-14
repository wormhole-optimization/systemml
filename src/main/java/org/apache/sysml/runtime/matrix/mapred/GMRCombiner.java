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
import java.util.Iterator;

import org.apache.hadoop.mapred.JobConf;
import org.apache.hadoop.mapred.OutputCollector;
import org.apache.hadoop.mapred.Reducer;
import org.apache.hadoop.mapred.Reporter;

import org.apache.sysml.runtime.matrix.data.MatrixCell;
import org.apache.sysml.runtime.matrix.data.MatrixIndexes;
import org.apache.sysml.runtime.matrix.data.MatrixPackedCell;
import org.apache.sysml.runtime.matrix.data.TaggedMatrixValue;


public class GMRCombiner extends ReduceBase
implements Reducer<MatrixIndexes, TaggedMatrixValue, MatrixIndexes, TaggedMatrixValue>
{
	
	//temporary variable
	private TaggedMatrixValue taggedbuffer=null;
	
	public void reduce(MatrixIndexes indexes, Iterator<TaggedMatrixValue> values,
			OutputCollector<MatrixIndexes, TaggedMatrixValue> out, Reporter report) 
	throws IOException 
	{
		long start=System.currentTimeMillis();
		
		cachedValues.reset();
		
		processAggregateInstructions(indexes, values, true);
		
		//output the matrices needed by the reducer
		outputInCombinerFromCachedValues(indexes, taggedbuffer, out);
		
		report.incrCounter(Counters.COMBINE_OR_REDUCE_TIME, System.currentTimeMillis()-start);
	}
	
	@Override
	public void configure(JobConf job)
	{
		super.configure(job);
		if(valueClass.equals(MatrixCell.class))
			valueClass=MatrixPackedCell.class;
		taggedbuffer=TaggedMatrixValue.createObject(valueClass);//new TaggedMatrixValue(valueClass);
	}
}


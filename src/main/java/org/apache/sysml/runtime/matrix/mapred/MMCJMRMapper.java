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

import org.apache.hadoop.io.Writable;
import org.apache.hadoop.mapred.JobConf;
import org.apache.hadoop.mapred.Mapper;
import org.apache.hadoop.mapred.OutputCollector;
import org.apache.hadoop.mapred.Reporter;

import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.instructions.mr.AggregateBinaryInstruction;
import org.apache.sysml.runtime.matrix.MatrixCharacteristics;
import org.apache.sysml.runtime.matrix.data.MatrixBlock;
import org.apache.sysml.runtime.matrix.data.TaggedFirstSecondIndexes;


public class MMCJMRMapper extends MapperBase 
implements Mapper<Writable, Writable, Writable, Writable>
{
	
	//the aggregate binary instruction for this mmcj job
	private AggregateBinaryInstruction aggBinInstruction;
	
	//tempory variable
	private TaggedFirstSecondIndexes taggedIndexes=new TaggedFirstSecondIndexes();
	
	//the tags to be output for the left and right matrice for the mmcj
	private byte tagForLeft=0;
	private byte tagForRight=1;
	
	@Override
	public void map(Writable rawKey, Writable rawValue,
			OutputCollector<Writable, Writable> out,
			Reporter reporter) throws IOException {
		
		commonMap(rawKey, rawValue, out, reporter);
	}

	@Override
	public void configure(JobConf job)
	{
		super.configure(job);
		AggregateBinaryInstruction[] ins;
		try {
			ins = MRJobConfiguration.getAggregateBinaryInstructions(job);
		} catch (DMLRuntimeException e) {
			throw new RuntimeException(e);
		}
		if(ins.length!=1)
			throw new RuntimeException("MMCJ only perform one aggregate binary instruction");
		aggBinInstruction=ins[0];
		
		//decide which matrix need to be cached for cross product
		MatrixCharacteristics dim1=MRJobConfiguration.getMatrixCharactristicsForBinAgg(job, aggBinInstruction.input1);
		MatrixCharacteristics dim2=MRJobConfiguration.getMatrixCharactristicsForBinAgg(job, aggBinInstruction.input2);
		if(dim1.getRows()>dim2.getCols())
		{
			tagForLeft=1;
			tagForRight=0;
		}
	}

	@Override
	protected void specialOperationsForActualMap(int index,
			OutputCollector<Writable, Writable> out, Reporter reporter)
			throws IOException {
		//apply all instructions
		processMapperInstructionsForMatrix(index);
		
		//process the mapper part of MMCJ
		processMMCJInMapperAndOutput(aggBinInstruction, tagForLeft, tagForRight, 
				taggedIndexes, out);
	}
	
	protected void processMMCJInMapperAndOutput(AggregateBinaryInstruction aggBinInstruction, 
			byte tagForLeft, byte tagForRight, TaggedFirstSecondIndexes taggedIndexes,
			OutputCollector<Writable, Writable> out) throws IOException
	{		
		//output the key value pair for the left matrix
		ArrayList<IndexedMatrixValue> blkList1 = cachedValues.get(aggBinInstruction.input1);
		if( blkList1 != null )
			for(IndexedMatrixValue result:blkList1)
				if(result!=null) {
					taggedIndexes.setTag(tagForLeft);
					taggedIndexes.setIndexes(result.getIndexes().getColumnIndex(), 
							result.getIndexes().getRowIndex());
					if( !((MatrixBlock)result.getValue()).isEmptyBlock() )
						out.collect(taggedIndexes, result.getValue());
				}
		
		//output the key value pair for the right matrix
		//Note: due to cached list reuse after first flush
		ArrayList<IndexedMatrixValue> blkList2 = cachedValues.get(aggBinInstruction.input2);
		if( blkList2 != null )
			for(IndexedMatrixValue result:blkList2)
				if(result!=null) {
					taggedIndexes.setTag(tagForRight);
					taggedIndexes.setIndexes(result.getIndexes().getRowIndex(), 
							result.getIndexes().getColumnIndex());
					if( !((MatrixBlock)result.getValue()).isEmptyBlock() ) 
						out.collect(taggedIndexes, result.getValue());
				}
	}
}

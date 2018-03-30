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
import org.apache.sysml.hops.OptimizerUtils;
import org.apache.sysml.runtime.instructions.mr.GroupedAggregateInstruction;
import org.apache.sysml.runtime.matrix.data.MatrixBlock;
import org.apache.sysml.runtime.matrix.data.MatrixIndexes;
import org.apache.sysml.runtime.matrix.data.MatrixValue;
import org.apache.sysml.runtime.matrix.data.TaggedMatrixIndexes;
import org.apache.sysml.runtime.matrix.data.WeightedCell;
import org.apache.sysml.runtime.matrix.operators.AggregateOperator;

public class GroupedAggMRMapper extends MapperBase
	implements Mapper<MatrixIndexes, MatrixValue, TaggedMatrixIndexes, WeightedCell>
{
		
	//block instructions that need to be performed in part by mapper
	protected ArrayList<ArrayList<GroupedAggregateInstruction>> groupAgg_instructions=new ArrayList<>();
	private MatrixIndexes outKeyValue=new MatrixIndexes();
	private TaggedMatrixIndexes outKey=new TaggedMatrixIndexes(outKeyValue, (byte)0);
	private WeightedCell outValue=new WeightedCell();

	@Override
	public void map(MatrixIndexes key, MatrixValue value,
			        OutputCollector<TaggedMatrixIndexes, WeightedCell> out, Reporter reporter) 
	    throws IOException 
	{
		for(int k=0; k<representativeMatrixes.size(); k++)
			for(GroupedAggregateInstruction ins : groupAgg_instructions.get(k))
			{
				//set the tag once for the block
				outKey.setTag(ins.output);
				
				//get block and unroll into weighted cells
				//(it will be in dense format)
				MatrixBlock block = (MatrixBlock) value;
				
				int rlen = block.getNumRows();
				int clen = block.getNumColumns();
				if( !ins.hasWeights() ) //w/o weights (input vector or matrix)
				{
					long coloff = (key.getColumnIndex()-1)*ins.getBclen();
					
					//local pre-aggregation for sum w/ known output dimensions
					if(ins.getOperator() instanceof AggregateOperator && ins.getNGroups() > 0 
						&& OptimizerUtils.isValidCPDimensions(ins.getNGroups(), block.getNumColumns()-1) ) 
					{
						try 
						{
							MatrixBlock group = block.slice(0, block.getNumRows()-1, 
									block.getNumColumns()-1, block.getNumColumns()-1, new MatrixBlock());
							MatrixBlock target = block.slice(0, block.getNumRows()-1, 
									0, block.getNumColumns()-2, new MatrixBlock());
								
							MatrixBlock tmp = group.groupedAggOperations(target, null, new MatrixBlock(), ins.getNGroups(), ins.getOperator());
							
							for(int i=0; i<tmp.getNumRows(); i++) {
								for( int j=0; j<tmp.getNumColumns(); j++ ) {
									double tmpval = tmp.quickGetValue(i, j);
									if( tmpval != 0 ) {
										outKeyValue.setIndexes(i+1,coloff+j+1);
										outValue.setValue(tmpval);
										outValue.setWeight(1);
										out.collect(outKey, outValue);
									}
								}
							}
						} 
						catch(Exception ex) {
							throw new IOException(ex);
						}
					}
					//general case without pre-aggregation
					else
					{
						for( int r=0; r<rlen; r++ ) {
							int group = (int)block.quickGetValue(r, clen-1);
							for( int c=0; c<clen-1; c++ ) {
								outKeyValue.setIndexes(group, coloff+c+1);
								outValue.setValue(block.quickGetValue(r, c));
								outValue.setWeight(1);
								out.collect(outKey, outValue);		
							}
						}
					}
				}
				else //w/ weights (input vector)
				{
					for( int r=0; r<rlen; r++ )
					{
						outKeyValue.setIndexes((int)block.quickGetValue(r, 1),1);
						outValue.setValue(block.quickGetValue(r, 0));
						outValue.setWeight(block.quickGetValue(r, 2));
						out.collect(outKey, outValue);		
					}
				}
			}
	}

	@Override
	protected void specialOperationsForActualMap(int index,
			OutputCollector<Writable, Writable> out, Reporter reporter)
			throws IOException 
	{
		
	}
	
	@Override
	public void configure(JobConf job)
	{
		super.configure(job);
		
		try 
		{
			GroupedAggregateInstruction[] grpaggIns = MRJobConfiguration.getGroupedAggregateInstructions(job);
			if( grpaggIns == null )
				throw new RuntimeException("no GroupAggregate Instructions found!");
			ArrayList<GroupedAggregateInstruction> vec = new ArrayList<>();
			for(int i=0; i<representativeMatrixes.size(); i++)
			{
				byte input=representativeMatrixes.get(i);
				for(GroupedAggregateInstruction ins : grpaggIns)
					if(ins.input == input)
						vec.add(ins);
				groupAgg_instructions.add(vec);
			}
		} 
		catch (Exception e) 
		{
			throw new RuntimeException(e);
		} 
	}
}

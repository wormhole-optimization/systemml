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
import java.util.HashMap;

import org.apache.hadoop.io.Writable;
import org.apache.hadoop.mapred.JobConf;
import org.apache.hadoop.mapred.Mapper;
import org.apache.hadoop.mapred.OutputCollector;
import org.apache.hadoop.mapred.Reporter;

import org.apache.sysml.runtime.matrix.data.MatrixCell;
import org.apache.sysml.runtime.matrix.data.MatrixPackedCell;
import org.apache.sysml.runtime.matrix.data.MatrixValue;
import org.apache.sysml.runtime.matrix.data.TaggedMatrixPackedCell;
import org.apache.sysml.runtime.matrix.data.TaggedMatrixValue;
import org.apache.sysml.runtime.util.MapReduceTool;

public class GMRMapper extends MapperBase 
implements Mapper<Writable, Writable, Writable, Writable>
{
	
	//whether this is a map only job
	private boolean mapOnlyJob=false;
	
	//the final result indexes that needed to be outputted for maponly job
	protected byte[] resultIndexes=null;
	protected byte[] resultDimsUnknown=null;

	//output converters for maponly job
	protected CollectMultipleConvertedOutputs collectFinalMultipleOutputs;

	//the counters to record how many nonZero cells have been produced for each output
	// for maponly job
	protected long[] resultsNonZeros=null;
	protected long[] resultsMaxRowDims=null;
	protected long[] resultsMaxColDims=null;
	protected String dimsUnknownFilePrefix;
	
	//cached reporter to report the number of nonZeros for each reduce task
	protected Reporter cachedReporter=null;
	
	protected String mapperID;
	
	//tempory variables
	private TaggedMatrixValue taggedValueBuffer=null;
	private HashMap<Byte, ArrayList<Integer>> tagMapping;
	
	//empty block filter flags
	private boolean _filterEmptyInputBlocks = false;
	
	@Override
	public void map(Writable rawKey, Writable rawValue, OutputCollector<Writable, Writable> out, Reporter reporter) 
		throws IOException 
	{
		//cache reporter for counters in close 
		cachedReporter = reporter;

		//empty block input filter
		if( _filterEmptyInputBlocks && ((MatrixValue)rawValue).isEmpty() )
			return;
		
		//default map runtime (input converters, call to overwritten special operations)
		commonMap(rawKey, rawValue, out, reporter);
	}
	
	@Override
	protected void specialOperationsForActualMap(int index, OutputCollector<Writable, Writable> out, Reporter reporter) 
		throws IOException 
	{		
		//apply all instructions
		processMapperInstructionsForMatrix(index);
		
		//output the results needed by the reducer
		if(mapOnlyJob)
			processMapFinalOutput(index, taggedValueBuffer, collectFinalMultipleOutputs, reporter, tagMapping);
		else
			processMapOutputToReducerForGMR(index, taggedValueBuffer, out);
	}

	protected void processMapOutputToReducerForGMR(int index, TaggedMatrixValue taggedValueBuffer, OutputCollector<Writable, Writable> out) 
		throws IOException
	{			
		for( byte output: outputIndexes.get(index) )
		{
			ArrayList<IndexedMatrixValue> results = cachedValues.get(output);
			if(results == null)
				continue;
			for(IndexedMatrixValue result : results)
			{
				if(result == null)
					continue;
				
				//prepare tagged output value
				//(special case for conversion from matrixcell to taggedmatrixpackedcell, e.g., ctable)
				if(valueClass.equals(MatrixCell.class))
					taggedValueBuffer.getBaseObject().copy(result.getValue());
				else
					taggedValueBuffer.setBaseObject(result.getValue());
				taggedValueBuffer.setTag(output);
				
				//collect output (exactly once)
				out.collect( result.getIndexes(), taggedValueBuffer);
			}
		}	
	}

	protected void processMapFinalOutput(int index,
			TaggedMatrixValue taggedValueBuffer, CollectMultipleConvertedOutputs collectFinalMultipleOutputs,
			Reporter reporter, HashMap<Byte, ArrayList<Integer>> tagMapping) throws IOException
	{
		for(byte output: outputIndexes.get(index))
		{
			ArrayList<IndexedMatrixValue> results= cachedValues.get(output);
			if(results==null)
				continue;
			for(IndexedMatrixValue result: results)
			{
				if(result==null)
					continue;
				
				//prepare tagged output value
				taggedValueBuffer.setBaseObject(result.getValue());
				taggedValueBuffer.setTag(output);
				
				//collect output (for all result indexes)				
				for( int outputIndex: tagMapping.get(output) )
				{
					collectOutput_N_Increase_Counter(
							result.getIndexes(), taggedValueBuffer.getBaseObject(), 
							outputIndex, reporter, collectFinalMultipleOutputs, 
							resultDimsUnknown, resultsNonZeros, resultsMaxRowDims, resultsMaxColDims);
				}
			}
		}	
		
	}
	
	@Override
	public void configure(JobConf job)
	{
		super.configure(job);
		
		mapperID = job.get(MRConfigurationNames.MR_TASK_ATTEMPT_ID);
		dimsUnknownFilePrefix = job.get("dims.unknown.file.prefix");
		
		_filterEmptyInputBlocks = allowsFilterEmptyInputBlocks();
		
		//assign the temporay vairables
		try {
			if(job.getMapOutputValueClass().equals(TaggedMatrixPackedCell.class))
				taggedValueBuffer=TaggedMatrixValue.createObject(MatrixPackedCell.class);
			else
				taggedValueBuffer=TaggedMatrixValue.createObject(valueClass);		
		} catch (Exception e) {
			throw new RuntimeException(e);
		}
		
		//decide whether it is a maponly job
		mapOnlyJob=(job.getNumReduceTasks()<=0);
		if(!mapOnlyJob)
			return;
		
		//get the indexes of the final output matrices
		resultIndexes=MRJobConfiguration.getResultIndexes(job);
		resultDimsUnknown = MRJobConfiguration.getResultDimsUnknown(job);
		
		//initialize SystemML Counters (defined in MRJobConfiguration)
		resultsNonZeros=new long[resultIndexes.length];
		resultsMaxRowDims=new long[resultIndexes.length];
		resultsMaxColDims=new long[resultIndexes.length];
		
		tagMapping=new HashMap<>();
		for(int i=0; i<resultIndexes.length; i++)
		{
			byte output=resultIndexes[i];
			ArrayList<Integer> vec=tagMapping.get(output);
			if(vec==null)
			{
				vec=new ArrayList<>();
				tagMapping.put(output, vec);
			}
			vec.add(i);
		}
		//for map only job, get the map output converters 
		collectFinalMultipleOutputs=MRJobConfiguration.getMultipleConvertedOutputs(job);
	}
	
	@Override
	public void close() throws IOException
	{
		if( cachedReporter!=null && mapOnlyJob )
		{
			//get and construct task id
			String[] parts = mapperID.split("_");
			String jobID = "job_" + parts[1] + "_" + parts[2];
			int taskid;
			if ( parts[0].equalsIgnoreCase("task")) {
				taskid = Integer.parseInt(parts[parts.length-1]);
			}
			else if ( parts[0].equalsIgnoreCase("attempt")) {
				taskid = Integer.parseInt(parts[parts.length-2]);
			}
			else {
				throw new RuntimeException("Unrecognized format for reducerID: " + mapperID);
			}
			
			//maintain unknown dimensions (if required, e.g., ctable)
			boolean dimsUnknown = false;
			for(int i=0; i<resultIndexes.length; i++) {
				cachedReporter.incrCounter(MRJobConfiguration.NUM_NONZERO_CELLS, Integer.toString(i), resultsNonZeros[i]);
				if ( resultDimsUnknown!=null && resultDimsUnknown[i] != (byte) 0 ) {
					dimsUnknown = true;
				}
			}
			if ( dimsUnknown ) {
				// every task creates a file with max_row and max_col dimensions found in that task
				MapReduceTool.writeDimsFile(dimsUnknownFilePrefix + "/" + jobID + "_dimsFile/" + "m_" + taskid , resultDimsUnknown, resultsMaxRowDims, resultsMaxColDims);
			}
		}
		
		if(collectFinalMultipleOutputs!=null)
			collectFinalMultipleOutputs.close();
	}
}

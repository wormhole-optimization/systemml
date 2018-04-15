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

package org.apache.sysml.runtime.controlprogram.parfor;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;

import org.apache.hadoop.fs.FileSystem;
import org.apache.hadoop.fs.Path;
import org.apache.hadoop.io.NullWritable;
import org.apache.hadoop.io.Text;
import org.apache.hadoop.mapred.FileInputFormat;
import org.apache.hadoop.mapred.FileOutputFormat;
import org.apache.hadoop.mapred.JobClient;
import org.apache.hadoop.mapred.JobConf;
import org.apache.sysml.api.DMLScript;
import org.apache.sysml.conf.ConfigurationManager;
import org.apache.sysml.conf.DMLConfig;
import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.controlprogram.caching.MatrixObject;
import org.apache.sysml.runtime.controlprogram.parfor.util.StagingFileUtils;
import org.apache.sysml.runtime.io.IOUtilFunctions;
import org.apache.sysml.runtime.matrix.MatrixCharacteristics;
import org.apache.sysml.runtime.matrix.MetaDataFormat;
import org.apache.sysml.runtime.matrix.data.InputInfo;
import org.apache.sysml.runtime.matrix.data.MatrixBlock;
import org.apache.sysml.runtime.matrix.data.MatrixCell;
import org.apache.sysml.runtime.matrix.data.MatrixIndexes;
import org.apache.sysml.runtime.matrix.data.OutputInfo;
import org.apache.sysml.runtime.matrix.data.TaggedMatrixBlock;
import org.apache.sysml.runtime.matrix.data.TaggedMatrixCell;
import org.apache.sysml.runtime.matrix.mapred.MRConfigurationNames;
import org.apache.sysml.runtime.matrix.mapred.MRJobConfiguration;
import org.apache.sysml.runtime.util.LocalFileUtils;
import org.apache.sysml.runtime.util.MapReduceTool;
import org.apache.sysml.utils.Statistics;

/**
 * MR job class for submitting parfor result merge MR jobs.
 * 
 */
public class ResultMergeRemoteMR extends ResultMerge
{
	private static final long serialVersionUID = 575681838941682037L;
	
	public static final byte COMPARE_TAG = 'c';
	public static final byte DATA_TAG = 'd';
	
	private long _pfid = -1;
	private int  _numMappers = -1;
	private int  _numReducers = -1;
	private int  _replication = -1;
	//private int  _max_retry = -1;
	private boolean _jvmReuse = false;

	public ResultMergeRemoteMR(MatrixObject out, MatrixObject[] in, String outputFilename, boolean accum,
		long pfid, int numMappers, int numReducers, int replication, int max_retry, boolean jvmReuse) 
	{
		super(out, in, outputFilename, accum);
		
		_pfid = pfid;
		_numMappers = numMappers;
		_numReducers = numReducers;
		_replication = replication;
		//_max_retry = max_retry;
		_jvmReuse = jvmReuse;
	}

	@Override
	public MatrixObject executeSerialMerge() {
		//graceful degradation to parallel merge
		return executeParallelMerge( _numMappers );
	}
	
	@Override
	public MatrixObject executeParallelMerge(int par) 
	{
		MatrixObject moNew = null; //always create new matrix object (required for nested parallelism)
		if( LOG.isTraceEnabled() )
			LOG.trace("ResultMerge (remote, mr): Execute serial merge for output "
				+_output.hashCode()+" (fname="+_output.getFileName()+")");
		
		try
		{
			//collect all relevant inputs
			Collection<String> srcFnames = new LinkedList<>();
			ArrayList<MatrixObject> inMO = new ArrayList<>();
			for( MatrixObject in : _inputs ) {
				//check for empty inputs (no iterations executed)
				if( in !=null && in != _output )  {
					//ensure that input file resides on disk
					in.exportData();
					//add to merge list
					srcFnames.add( in.getFileName() );
					inMO.add(in);
				}
			}

			if( !srcFnames.isEmpty() )
			{
				//ensure that outputfile (for comparison) resides on disk
				_output.exportData();
				
				//actual merge
				MetaDataFormat metadata = (MetaDataFormat) _output.getMetaData();
				MatrixCharacteristics mcOld = metadata.getMatrixCharacteristics();
				
				String fnameCompare = _output.getFileName();
				if( mcOld.getNonZeros()==0 )
					fnameCompare = null; //no compare required
				
				executeMerge(fnameCompare, _outputFName, srcFnames.toArray(new String[0]), 
						     metadata.getInputInfo(),metadata.getOutputInfo(), mcOld.getRows(), mcOld.getCols(),
						     mcOld.getRowsPerBlock(), mcOld.getColsPerBlock());
				
				//create new output matrix (e.g., to prevent potential export<->read file access conflict
				moNew = new MatrixObject(_output.getValueType(), _outputFName);
				OutputInfo oiOld = metadata.getOutputInfo();
				InputInfo iiOld = metadata.getInputInfo();
				MatrixCharacteristics mc = new MatrixCharacteristics(mcOld);
				mc.setNonZeros(_isAccum ? -1 : computeNonZeros(_output, inMO));
				MetaDataFormat meta = new MetaDataFormat(mc,oiOld,iiOld);
				moNew.setMetaData( meta );
			}
			else
			{
				moNew = _output; //return old matrix, to prevent copy
			}
		}
		catch(Exception ex)
		{
			throw new DMLRuntimeException(ex);
		}

		//LOG.trace("ResultMerge (local, file): Executed serial merge for output "+_output.getVarName()+" (fname="+_output.getFileName()+") in "+time.stop()+"ms");
		
		return moNew;
	}

	@SuppressWarnings({ "unused", "deprecation" })
	protected void executeMerge(String fname, String fnameNew, String[] srcFnames, InputInfo ii, OutputInfo oi, long rlen, long clen, int brlen, int bclen)
	{
		String jobname = "ParFor-RMMR";
		long t0 = DMLScript.STATISTICS ? System.nanoTime() : 0;
		
		JobConf job = new JobConf( ResultMergeRemoteMR.class );
		job.setJobName(jobname+_pfid);

		//maintain dml script counters
		Statistics.incrementNoOfCompiledMRJobs();
		
		//warning for textcell/binarycell without compare
		boolean withCompare = (fname!=null);
		if( (oi == OutputInfo.TextCellOutputInfo || oi == OutputInfo.BinaryCellOutputInfo) && !withCompare && ResultMergeLocalFile.ALLOW_COPY_CELLFILES )
			LOG.warn("Result merge for "+OutputInfo.outputInfoToString(oi)+" without compare can be realized more efficiently with LOCAL_FILE than REMOTE_MR.");
			
		try
		{
			Path pathCompare = null;
			Path pathNew = new Path(fnameNew);
			
			/////
			//configure the MR job
			if( withCompare ) {
				FileSystem fs = IOUtilFunctions.getFileSystem(pathNew, job);
				pathCompare = new Path(fname).makeQualified(fs);
				MRJobConfiguration.setResultMergeInfo(job, pathCompare.toString(), _isAccum, ii, 
					LocalFileUtils.getWorkingDir(LocalFileUtils.CATEGORY_RESULTMERGE), rlen, clen, brlen, bclen);
			}
			else
				MRJobConfiguration.setResultMergeInfo(job, "null", _isAccum, ii,
					LocalFileUtils.getWorkingDir(LocalFileUtils.CATEGORY_RESULTMERGE), rlen, clen, bclen, bclen);
			
			
			//set mappers, reducers, combiners
			job.setMapperClass(ResultMergeRemoteMapper.class); 
			job.setReducerClass(ResultMergeRemoteReducer.class);
			
			if( oi == OutputInfo.TextCellOutputInfo )
			{
				job.setMapOutputKeyClass(MatrixIndexes.class);
				job.setMapOutputValueClass(TaggedMatrixCell.class);
				job.setOutputKeyClass(NullWritable.class);
				job.setOutputValueClass(Text.class);
			}
			else if( oi == OutputInfo.BinaryCellOutputInfo )
			{
				job.setMapOutputKeyClass(MatrixIndexes.class);
				job.setMapOutputValueClass(TaggedMatrixCell.class);
				job.setOutputKeyClass(MatrixIndexes.class);
				job.setOutputValueClass(MatrixCell.class);
			}
			else if ( oi == OutputInfo.BinaryBlockOutputInfo )
			{
				//setup partitioning, grouping, sorting for composite key (old API)
				job.setPartitionerClass(ResultMergeRemotePartitioning.class); //partitioning
		        job.setOutputValueGroupingComparator(ResultMergeRemoteGrouping.class); //grouping
		        job.setOutputKeyComparatorClass(ResultMergeRemoteSorting.class); //sorting
		        
				job.setMapOutputKeyClass(ResultMergeTaggedMatrixIndexes.class);
				job.setMapOutputValueClass(TaggedMatrixBlock.class);
				job.setOutputKeyClass(MatrixIndexes.class);
				job.setOutputValueClass(MatrixBlock.class);
			}
			
			//set input format 
			job.setInputFormat(ii.inputFormatClass);
			
			//set the input path 
			Path[] paths = null;
			if( withCompare ) {
				paths= new Path[ srcFnames.length+1 ];
				paths[0] = pathCompare;
				for(int i=1; i<paths.length; i++)
					paths[i] = new Path( srcFnames[i-1] ); 
			}
			else {
				paths= new Path[ srcFnames.length ];
				for(int i=0; i<paths.length; i++)
					paths[i] = new Path( srcFnames[i] );
			}
		    FileInputFormat.setInputPaths(job, paths);
			
		    //set output format
		    job.setOutputFormat(oi.outputFormatClass);
		    
		    //set output path
		    MapReduceTool.deleteFileIfExistOnHDFS(fnameNew);
		    FileOutputFormat.setOutputPath(job, pathNew);
		    

			//////
			//set optimization parameters

			//set the number of mappers and reducers 
		    //job.setNumMapTasks( _numMappers ); //use default num mappers
		    long reducerGroups = _numReducers;
		    if( oi == OutputInfo.BinaryBlockOutputInfo )
		    	reducerGroups = Math.max(rlen/brlen,1) * Math.max(clen/bclen, 1); 
		    else //textcell/binarycell
		    	reducerGroups = Math.max((rlen*clen)/StagingFileUtils.CELL_BUFFER_SIZE, 1);
			job.setNumReduceTasks( (int)Math.min( _numReducers, reducerGroups) ); 	

			
			//disable automatic tasks timeouts and speculative task exec
			job.setInt(MRConfigurationNames.MR_TASK_TIMEOUT, 0);
			job.setMapSpeculativeExecution(false);
			
			//set up preferred custom serialization framework for binary block format
			if( MRJobConfiguration.USE_BINARYBLOCK_SERIALIZATION )
				MRJobConfiguration.addBinaryBlockSerializationFramework( job );
			
			//set up custom map/reduce configurations 
			DMLConfig config = ConfigurationManager.getDMLConfig();
			MRJobConfiguration.setupCustomMRConfigurations(job, config);
			
			//enables the reuse of JVMs (multiple tasks per MR task)
			if( _jvmReuse )
				job.setNumTasksToExecutePerJvm(-1); //unlimited
			
			//enables compression - not conclusive for different codecs (empirically good compression ratio, but significantly slower)
			//job.set(MRConfigurationNames.MR_MAP_OUTPUT_COMPRESS, "true");
			//job.set(MRConfigurationNames.MR_MAP_OUTPUT_COMPRESS_CODEC, "org.apache.hadoop.io.compress.GzipCodec");
			
			//set the replication factor for the results
			job.setInt(MRConfigurationNames.DFS_REPLICATION, _replication);
			
			//set the max number of retries per map task
		    //  disabled job-level configuration to respect cluster configuration
			//  note: this refers to hadoop2, hence it never had effect on mr1
			//job.setInt(MRConfigurationNames.MR_MAP_MAXATTEMPTS, _max_retry);
			
			//set unique working dir
			MRJobConfiguration.setUniqueWorkingDir(job);
			
			/////
			// execute the MR job	
			
			JobClient.runJob(job);
		
			//maintain dml script counters
			Statistics.incrementNoOfExecutedMRJobs();
		}
		catch(Exception ex)
		{
			throw new DMLRuntimeException(ex);
		}
		
		if( DMLScript.STATISTICS ){
			long t1 = System.nanoTime();
			Statistics.maintainCPHeavyHitters("MR-Job_"+jobname, t1-t0);
		}
	}
}

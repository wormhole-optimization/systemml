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


package org.apache.sysml.runtime.matrix;

import java.io.PrintWriter;
import java.util.HashSet;
import java.util.PrimitiveIterator;
import java.util.stream.LongStream;

import org.apache.commons.logging.Log;
import org.apache.commons.logging.LogFactory;
import org.apache.commons.math3.random.Well1024a;
import org.apache.hadoop.fs.FileSystem;
import org.apache.hadoop.fs.Path;
import org.apache.hadoop.io.Writable;
import org.apache.hadoop.mapred.Counters.Group;
import org.apache.hadoop.mapred.JobClient;
import org.apache.hadoop.mapred.JobConf;
import org.apache.hadoop.mapred.RunningJob;
import org.apache.sysml.conf.ConfigurationManager;
import org.apache.sysml.conf.DMLConfig;
import org.apache.sysml.lops.Lop;
import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.controlprogram.parfor.stat.InfrastructureAnalyzer;
import org.apache.sysml.runtime.instructions.MRInstructionParser;
import org.apache.sysml.runtime.instructions.MRJobInstruction;
import org.apache.sysml.runtime.instructions.mr.DataGenMRInstruction;
import org.apache.sysml.runtime.instructions.mr.MRInstruction;
import org.apache.sysml.runtime.instructions.mr.MRInstruction.MRINSTRUCTION_TYPE;
import org.apache.sysml.runtime.instructions.mr.RandInstruction;
import org.apache.sysml.runtime.instructions.mr.SeqInstruction;
import org.apache.sysml.runtime.io.IOUtilFunctions;
import org.apache.sysml.runtime.matrix.data.InputInfo;
import org.apache.sysml.runtime.matrix.data.LibMatrixDatagen;
import org.apache.sysml.runtime.matrix.data.MatrixIndexes;
import org.apache.sysml.runtime.matrix.data.OutputInfo;
import org.apache.sysml.runtime.matrix.data.TaggedMatrixBlock;
import org.apache.sysml.runtime.matrix.mapred.DataGenMapper;
import org.apache.sysml.runtime.matrix.mapred.GMRCombiner;
import org.apache.sysml.runtime.matrix.mapred.GMRReducer;
import org.apache.sysml.runtime.matrix.mapred.MRConfigurationNames;
import org.apache.sysml.runtime.matrix.mapred.MRJobConfiguration;
import org.apache.sysml.runtime.matrix.mapred.MRJobConfiguration.ConvertTarget;
import org.apache.sysml.runtime.matrix.mapred.MRJobConfiguration.MatrixChar_N_ReducerGroups;
import org.apache.sysml.runtime.util.MapReduceTool;
import org.apache.sysml.runtime.util.UtilFunctions;
import org.apache.sysml.yarn.DMLAppMasterUtils;
import org.apache.sysml.yarn.ropt.YarnClusterAnalyzer;


/**
 * <p>Rand MapReduce job which creates random objects.</p>
 * 
 */
public class DataGenMR
{
	private static final Log LOG = LogFactory.getLog(DataGenMR.class.getName());
	
	private DataGenMR() {
		//prevent instantiation via private constructor
	}
	
	/**
	 * <p>Starts a Rand MapReduce job which will produce one or more random objects.</p>
	 * 
	 * @param inst MR job instruction
	 * @param dataGenInstructions array of data gen instructions
	 * @param instructionsInMapper instructions in mapper
	 * @param aggInstructionsInReducer aggregate instructions in reducer
	 * @param otherInstructionsInReducer other instructions in reducer
	 * @param numReducers number of reducers
	 * @param replication file replication
	 * @param resultIndexes result indexes for each random object
	 * @param dimsUnknownFilePrefix file path prefix when dimensions unknown
	 * @param outputs output file for each random object
	 * @param outputInfos output information for each random object
	 * @return matrix characteristics for each random object
	 * @throws Exception if Exception occurs
	 */
	public static JobReturn runJob(MRJobInstruction inst, String[] dataGenInstructions, 
			String instructionsInMapper, String aggInstructionsInReducer, String otherInstructionsInReducer, 
			int numReducers, int replication, byte[] resultIndexes, String dimsUnknownFilePrefix, 
			String[] outputs, OutputInfo[] outputInfos) 
	throws Exception
	{
		JobConf job = new JobConf(DataGenMR.class);
		job.setJobName("DataGen-MR");
		
		//whether use block representation or cell representation
		MRJobConfiguration.setMatrixValueClass(job, true);
		
		
		byte[] realIndexes=new byte[dataGenInstructions.length];
		for(byte b=0; b<realIndexes.length; b++)
			realIndexes[b]=b;
		
		String[] inputs=new String[dataGenInstructions.length];
		InputInfo[] inputInfos = new InputInfo[dataGenInstructions.length];
		long[] rlens=new long[dataGenInstructions.length];
		long[] clens=new long[dataGenInstructions.length];
		int[] brlens=new int[dataGenInstructions.length];
		int[] bclens=new int[dataGenInstructions.length];
		
		FileSystem fs = FileSystem.get(job);
		String dataGenInsStr="";
		int numblocks=0;
		int maxbrlen=-1, maxbclen=-1;
		double maxsparsity = -1;
		
		for(int i = 0; i < dataGenInstructions.length; i++)
		{
			dataGenInsStr=dataGenInsStr+Lop.INSTRUCTION_DELIMITOR+dataGenInstructions[i];
			
			MRInstruction mrins = MRInstructionParser.parseSingleInstruction(dataGenInstructions[i]);
			MRINSTRUCTION_TYPE mrtype = mrins.getMRInstructionType();
			DataGenMRInstruction genInst = (DataGenMRInstruction) mrins;
			
			rlens[i]  = genInst.getRows();
			clens[i]  = genInst.getCols();
			brlens[i] = genInst.getRowsInBlock();
			bclens[i] = genInst.getColsInBlock();
			
			maxbrlen = Math.max(maxbrlen, brlens[i]);
			maxbclen = Math.max(maxbclen, bclens[i]);

			if ( mrtype == MRINSTRUCTION_TYPE.Rand ) 
			{
				RandInstruction randInst = (RandInstruction) mrins;
				inputs[i]=LibMatrixDatagen.generateUniqueSeedPath(genInst.getBaseDir());
				maxsparsity = Math.max(maxsparsity, randInst.getSparsity());
				
				PrintWriter pw = null;
				try {
					pw = new PrintWriter(fs.create(new Path(inputs[i])));
					
					//for obj reuse and preventing repeated buffer re-allocations
					StringBuilder sb = new StringBuilder();
					
					//seed generation
					Well1024a bigrand = LibMatrixDatagen.setupSeedsForRand(randInst.getSeed());
					LongStream nnz = LibMatrixDatagen.computeNNZperBlock(rlens[i], clens[i], brlens[i], bclens[i], randInst.getSparsity());
					PrimitiveIterator.OfLong nnzIter = nnz.iterator();
					for(long r = 0; r < rlens[i]; r += brlens[i]) {
						long curBlockRowSize = Math.min(brlens[i], (rlens[i] - r));
						for(long c = 0; c < clens[i]; c += bclens[i])
						{
							long curBlockColSize = Math.min(bclens[i], (clens[i] - c));
							
							sb.append((r / brlens[i]) + 1);
							sb.append(',');
							sb.append((c / bclens[i]) + 1);
							sb.append(',');
							sb.append(curBlockRowSize);
							sb.append(',');
							sb.append(curBlockColSize);
							sb.append(',');
							sb.append(nnzIter.nextLong());
							sb.append(',');
							sb.append(bigrand.nextLong());
							pw.println(sb.toString());
							sb.setLength(0);
							numblocks++;
						}
					}
				}
				finally {
					IOUtilFunctions.closeSilently(pw);
				}
				inputInfos[i] = InputInfo.TextCellInputInfo;
			}
			else if ( mrtype == MRINSTRUCTION_TYPE.Seq ) {
				SeqInstruction seqInst = (SeqInstruction) mrins;
				inputs[i]=genInst.getBaseDir() + System.currentTimeMillis()+".seqinput";
				maxsparsity = 1.0; //always dense
				
				double from = seqInst.fromValue;
				double to = seqInst.toValue;
				double incr = seqInst.incrValue;

				//handle default 1 to -1 for special case of from>to
				incr = LibMatrixDatagen.updateSeqIncr(from, to, incr);
				
				// Correctness checks on (from, to, incr)
				boolean neg = (from > to);
				if ( incr == 0 )
					throw new DMLRuntimeException("Invalid value for \"increment\" in seq().");
				
				if (neg != (incr < 0) )
					throw new DMLRuntimeException("Wrong sign for the increment in a call to seq()");
				
				// Compute the number of rows in the sequence
				long numrows = UtilFunctions.getSeqLength(from, to, incr);
				if ( rlens[i] > 0 ) {
					if ( numrows != rlens[i] )
						throw new DMLRuntimeException("Unexpected error while processing sequence instruction. Expected number of rows does not match given number: " + rlens[i] + " != " + numrows);
				}
				else {
					rlens[i] = numrows;
				}
				
				if ( clens[i] >0 && clens[i] != 1)
					throw new DMLRuntimeException("Unexpected error while processing sequence instruction. Number of columns (" + clens[i] + ") must be equal to 1.");
				else 
					clens[i] = 1;

				PrintWriter pw = null;
				try {
					pw = new PrintWriter(fs.create(new Path(inputs[i])));
					StringBuilder sb = new StringBuilder();
					
					double temp = from;
					double block_from, block_to;
					for(long r = 0; r < rlens[i]; r += brlens[i]) {
						long curBlockRowSize = Math.min(brlens[i], (rlens[i] - r));
						
						// block (bid_i,bid_j) generates a sequence from the interval [block_from, block_to] (inclusive of both end points of the interval) 
						long bid_i = ((r / brlens[i]) + 1);
						long bid_j = 1;
						block_from = temp;
						block_to   = temp+(curBlockRowSize-1)*incr;
						temp = block_to + incr; // next block starts from here
						
						sb.append(bid_i);
						sb.append(',');
						sb.append(bid_j);
						sb.append(',');
						sb.append(block_from);
						sb.append(',');
						sb.append(block_to);
						sb.append(',');
						sb.append(incr);
						
						pw.println(sb.toString());
						sb.setLength(0);
						numblocks++;
					}
				}
				finally {
					IOUtilFunctions.closeSilently(pw);
				}
				inputInfos[i] = InputInfo.TextCellInputInfo;
			} else {
				throw new DMLRuntimeException("Unexpected Data Generation Instruction Type: " + mrtype );
			}
		}
		dataGenInsStr=dataGenInsStr.substring(1);//remove the first ","
		RunningJob runjob;
		MatrixCharacteristics[] stats;
		try{
			//set up the block size
			MRJobConfiguration.setBlocksSizes(job, realIndexes, brlens, bclens);
			
			//set up the input files and their format information
			MRJobConfiguration.setUpMultipleInputs(job, realIndexes, inputs, inputInfos, brlens, bclens, false, ConvertTarget.BLOCK);
			
			//set up the dimensions of input matrices
			MRJobConfiguration.setMatricesDimensions(job, realIndexes, rlens, clens);
			MRJobConfiguration.setDimsUnknownFilePrefix(job, dimsUnknownFilePrefix);
			
			//set up the block size
			MRJobConfiguration.setBlocksSizes(job, realIndexes, brlens, bclens);
			
			//set up the rand Instructions
			MRJobConfiguration.setRandInstructions(job, dataGenInsStr);
			
			//set up unary instructions that will perform in the mapper
			MRJobConfiguration.setInstructionsInMapper(job, instructionsInMapper);
			
			//set up the aggregate instructions that will happen in the combiner and reducer
			MRJobConfiguration.setAggregateInstructions(job, aggInstructionsInReducer);
			
			//set up the instructions that will happen in the reducer, after the aggregation instrucions
			MRJobConfiguration.setInstructionsInReducer(job, otherInstructionsInReducer);
			
			//set up the replication factor for the results
			job.setInt(MRConfigurationNames.DFS_REPLICATION, replication);
			
			//set up map/reduce memory configurations (if in AM context)
			DMLConfig config = ConfigurationManager.getDMLConfig();
			DMLAppMasterUtils.setupMRJobRemoteMaxMemory(job, config);
			
			//set up custom map/reduce configurations 
			MRJobConfiguration.setupCustomMRConfigurations(job, config);
			
			//determine degree of parallelism (nmappers: 1<=n<=capacity)
			//TODO use maxsparsity whenever we have a way of generating sparse rand data
			int capacity = InfrastructureAnalyzer.getRemoteParallelMapTasks();
			long dfsblocksize = InfrastructureAnalyzer.getHDFSBlockSize();
			//correction max number of mappers on yarn clusters
			if( InfrastructureAnalyzer.isYarnEnabled() )
				capacity = (int)Math.max( capacity, YarnClusterAnalyzer.getNumCores() );
			int nmapers = Math.max(Math.min((int)(8*maxbrlen*maxbclen*(long)numblocks/dfsblocksize), capacity),1);
			job.setNumMapTasks(nmapers);
			
			//set up what matrices are needed to pass from the mapper to reducer
			HashSet<Byte> mapoutputIndexes=MRJobConfiguration.setUpOutputIndexesForMapper(job, realIndexes,  dataGenInsStr, instructionsInMapper, null, aggInstructionsInReducer, otherInstructionsInReducer, resultIndexes);
			
			MatrixChar_N_ReducerGroups ret=MRJobConfiguration.computeMatrixCharacteristics(job, realIndexes, dataGenInsStr,
					instructionsInMapper, null, aggInstructionsInReducer, null, otherInstructionsInReducer, 
					resultIndexes, mapoutputIndexes, false);
			stats=ret.stats;
			
			//set up the number of reducers
			MRJobConfiguration.setNumReducers(job, ret.numReducerGroups, numReducers);
			
			// print the complete MRJob instruction
			if (LOG.isTraceEnabled())
				inst.printCompleteMRJobInstruction(stats);
			
			// Update resultDimsUnknown based on computed "stats"
			byte[] resultDimsUnknown = new byte[resultIndexes.length]; 
			for ( int i=0; i < resultIndexes.length; i++ ) { 
				if ( stats[i].getRows() == -1 || stats[i].getCols() == -1 ) {
					resultDimsUnknown[i] = (byte) 1;
				}
				else {
					resultDimsUnknown[i] = (byte) 0;
				}
			}
			
			boolean mayContainCtable = instructionsInMapper.contains("ctabletransform") ||instructionsInMapper.contains("groupedagg") ; 
			
			//set up the multiple output files, and their format information
			MRJobConfiguration.setUpMultipleOutputs(job, resultIndexes, resultDimsUnknown, outputs, outputInfos, true, mayContainCtable);
			
			// configure mapper and the mapper output key value pairs
			job.setMapperClass(DataGenMapper.class);
			if(numReducers==0)
			{
				job.setMapOutputKeyClass(Writable.class);
				job.setMapOutputValueClass(Writable.class);
			}else
			{
				job.setMapOutputKeyClass(MatrixIndexes.class);
				job.setMapOutputValueClass(TaggedMatrixBlock.class);
			}
			
			//set up combiner
			if(numReducers!=0 && aggInstructionsInReducer!=null 
					&& !aggInstructionsInReducer.isEmpty())
				job.setCombinerClass(GMRCombiner.class);
		
			//configure reducer
			job.setReducerClass(GMRReducer.class);
			//job.setReducerClass(PassThroughReducer.class);

			// By default, the job executes in "cluster" mode.
			// Determine if we can optimize and run it in "local" mode.
			MatrixCharacteristics[] inputStats = new MatrixCharacteristics[inputs.length];
			for ( int i=0; i < inputs.length; i++ ) {
				inputStats[i] = new MatrixCharacteristics(rlens[i], clens[i], brlens[i], bclens[i]);
			}
			
			//set unique working dir
			MRJobConfiguration.setUniqueWorkingDir(job);
			
			
			runjob=JobClient.runJob(job);
			
			/* Process different counters */
			
			Group group=runjob.getCounters().getGroup(MRJobConfiguration.NUM_NONZERO_CELLS);
			for(int i=0; i<resultIndexes.length; i++) {
				// number of non-zeros
				stats[i].setNonZeros(group.getCounter(Integer.toString(i)));
			}
			
			String dir = dimsUnknownFilePrefix + "/" + runjob.getID().toString() + "_dimsFile";
			stats = MapReduceTool.processDimsFiles(dir, stats);
			MapReduceTool.deleteFileIfExistOnHDFS(dir);
			
		}
		finally
		{
			for(String input: inputs)
				MapReduceTool.deleteFileIfExistOnHDFS(new Path(input), job);
		}
		
		return new JobReturn(stats, outputInfos, runjob.isSuccessful());
	}
}

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

package org.apache.sysml.runtime.controlprogram.parfor.mqo;

import java.util.LinkedList;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import org.apache.sysml.lops.runtime.RunMRJobs;
import org.apache.sysml.runtime.instructions.MRJobInstruction;
import org.apache.sysml.runtime.matrix.JobReturn;
import org.apache.sysml.runtime.matrix.MatrixCharacteristics;
import org.apache.sysml.runtime.matrix.data.Pair;
import org.apache.sysml.utils.Statistics;

/**
 * 
 * Extensions: (1) take number of running jobs into account,
 * (2) compute timeout threshold based on max and last job execution time.
 */
public class PiggybackingWorkerUtilDecayParallel extends PiggybackingWorker
{

	//internal configuration parameters
	private static long MIN_MERGE_INTERVAL = 1000;
	private static double UTILIZATION_DECAY = 0.5; //decay per minute 
	
	//thread pool for parallel submit
	private ExecutorService _parSubmit = null;
	
	private long _minTime = -1;
	private double _utilDecay = -1; 
	private int _par = -1;
	
	public PiggybackingWorkerUtilDecayParallel(int par)
	{
		this( MIN_MERGE_INTERVAL, 
			  UTILIZATION_DECAY, 
			  par );
	}
	
	public PiggybackingWorkerUtilDecayParallel( long minInterval, double utilDecay, int par )
	{
		_minTime = minInterval;
		_utilDecay = utilDecay;
		_par = par;
		
		//init thread pool
		_parSubmit = Executors.newFixedThreadPool(_par);
	}

	@Override 
	public void setStopped()
	{
		//parent logic
		super.setStopped();
		
		//explicitly stop the thread pool
		_parSubmit.shutdown();
	}
	
	@Override
	public void run() 
	{
		long lastTime = System.currentTimeMillis();
		
		while( !_stop )
		{
			try
			{
				long currentTime = System.currentTimeMillis()+1; //ensure > lastTime
				
				// wait until next submission
				Thread.sleep(_minTime); //wait at least minTime
				
				//continue if (prevent cluster status requests)
				if( RuntimePiggybacking.isEmptyJobPool() )
					continue;
				
				double util = RuntimePiggybackingUtils.getCurrentClusterUtilization();
				double utilThreshold = 1-Math.pow(_utilDecay, Math.ceil(((double)currentTime-lastTime)/60000));
				
				//continue to collect jobs if cluster util too high (decay to prevent starvation)
				if( util > utilThreshold ) { //cluster utilization condition
					continue; //1min - >50%, 2min - >75%, 3min - >87.5%, 4min - > 93.7%
				}
				
				// pick job type with largest number of jobs
				LinkedList<Pair<Long,MRJobInstruction>> workingSet = RuntimePiggybacking.getMaxWorkingSet();
				if( workingSet == null )
					continue; //empty pool
				
				// merge jobs (if possible)
				LinkedList<MergedMRJobInstruction> mergedWorkingSet = mergeMRJobInstructions(workingSet);
				
				// submit all resulting jobs (parallel submission)
				for( MergedMRJobInstruction minst : mergedWorkingSet )
				{
					//submit job and return results if finished
					_parSubmit.execute(new MRJobSubmitTask(minst));
				}
				
				lastTime = currentTime;
			}
			catch(Exception ex)
			{
				throw new RuntimeException(ex);
			}
		}
	}

	public class MRJobSubmitTask implements Runnable
	{
		private MergedMRJobInstruction _minst = null;
		
		public MRJobSubmitTask( MergedMRJobInstruction minst )
		{
			_minst = minst;
		}
		
		@Override
		public void run() 
		{
			try
			{
				// submit mr job
				JobReturn mret = RunMRJobs.submitJob(_minst.inst);
				Statistics.incrementNoOfExecutedMRJobs();
				
				// error handling
				if( !mret.successful )
					LOG.error("Failed to run merged mr-job instruction:\n"+_minst.inst.toString()); 
				
				// split job return
				LinkedList<JobReturn> ret = new LinkedList<>();
				for( Long id : _minst.ids ){
					ret.add( _minst.constructJobReturn(id, mret) );
					Statistics.decrementNoOfExecutedMRJobs();
				}
				putJobResults(_minst.ids, ret);
			}
			catch(Exception ex)
			{
				//log error and merged instruction
				LOG.error("Failed to run merged mr-job instruction:\n"+_minst.inst.toString(),ex); 
				
				//handle unsuccessful job returns for failed job 
				//(otherwise clients would literally wait forever for results)
				LinkedList<JobReturn> ret = new LinkedList<>();
				for( Long id : _minst.ids ){
					JobReturn fret = new JobReturn(new MatrixCharacteristics[_minst.outIxLens.get(id)], false); 
					ret.add( _minst.constructJobReturn(id, fret) );
					Statistics.decrementNoOfExecutedMRJobs();
				}
				// make job returns available and notify waiting clients
				putJobResults(_minst.ids, ret);
			}
		}
		
	}
	
}

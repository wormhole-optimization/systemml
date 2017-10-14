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

import java.util.HashMap;
import java.util.LinkedList;

import org.apache.commons.logging.Log;
import org.apache.commons.logging.LogFactory;

import org.apache.sysml.runtime.controlprogram.parfor.stat.Timing;
import org.apache.sysml.runtime.instructions.MRJobInstruction;
import org.apache.sysml.runtime.matrix.JobReturn;
import org.apache.sysml.runtime.matrix.data.Pair;

public abstract class PiggybackingWorker extends Thread
{
	
	
	protected static final Log LOG = LogFactory.getLog(PiggybackingWorker.class.getName());

	protected HashMap<Long, JobReturn> _results = null;	
	protected boolean _stop;
	
	protected PiggybackingWorker()
	{
		_results = new HashMap<>();
		_stop = false;
	}

	public void setStopped()
	{
		_stop = true;
	}

	public synchronized JobReturn getJobResult( long instID ) 
		throws InterruptedException
	{
		JobReturn ret = null;
				
		while( ret == null )
		{
			//wait for new results 
			wait();
			
			//obtain job return (if available)
			ret = _results.remove( instID );
		}
		
		return ret;
	}

	protected synchronized void putJobResults( LinkedList<Long> ids, LinkedList<JobReturn> results )
	{
		//make job returns available
		for( int i=0; i<ids.size(); i++ )
			_results.put(ids.get(i), results.get(i));
	
		//notify all waiting threads
		notifyAll();
	}

	protected LinkedList<MergedMRJobInstruction> mergeMRJobInstructions( LinkedList<Pair<Long,MRJobInstruction>> workingSet ) 
		throws IllegalAccessException
	{
		LinkedList<MergedMRJobInstruction> ret = new LinkedList<>();
		Timing time = new Timing(true);
		
		//NOTE currently all merged into one (might be invalid due to memory constraints)
		MergedMRJobInstruction minst = new MergedMRJobInstruction();
		for( Pair<Long,MRJobInstruction> inst : workingSet )
		{
			long instID = inst.getKey();
			MRJobInstruction instVal = inst.getValue();
			int numOutputs = instVal.getOutputs().length;
			
			//append to current merged instruction
			if( minst.inst==null )
			{
				//deep copy first instruction
				minst.inst = new MRJobInstruction( instVal );	
				minst.addInstructionMetaData( instID, 0, numOutputs );
			}
			else
			{	
				//merge other instructions
				if( minst.inst.isMergableMRJobInstruction( instVal ) )
				{
					//add instruction to open merged instruction
					int offOutputs = minst.inst.getOutputs().length; //before merge
					minst.inst.mergeMRJobInstruction( instVal );
					minst.addInstructionMetaData(instID, offOutputs, numOutputs);	
				}
				else
				{
					//close current merged instruction
					ret.add(minst); 
					//open new merged instruction
					minst = new MergedMRJobInstruction();
					minst.inst = new MRJobInstruction( instVal );	
					minst.addInstructionMetaData( instID, 0, numOutputs );
				}
			}
		}
		//close last open merged instruction
		ret.add(minst);
		
		//output log info for better understandability for users
		LOG.info("Merged MR-Job instructions: "+workingSet.size()+" --> "+ret.size()+" in "+time.stop()+"ms.");
		
		return ret;
	}
}

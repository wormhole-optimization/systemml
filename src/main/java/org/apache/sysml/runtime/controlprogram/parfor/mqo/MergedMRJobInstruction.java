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

import org.apache.sysml.runtime.instructions.MRJobInstruction;
import org.apache.sysml.runtime.matrix.JobReturn;
import org.apache.sysml.runtime.matrix.MetaData;

/**
 * Merged MR Job instruction to hold the actually merged instruction as well as offsets of
 * result indexes in order to split result meta data after successful execution.
 * 
 */
public class MergedMRJobInstruction 
{
	
	protected MRJobInstruction inst;
	protected LinkedList<Long> ids;
	protected HashMap<Long,Integer> outIxOffs;
	protected HashMap<Long,Integer> outIxLens;
	
	public MergedMRJobInstruction()
	{
		ids = new LinkedList<>();
		outIxOffs = new HashMap<>();
		outIxLens = new HashMap<>();
	}
	
	public void addInstructionMetaData(long instID, int outIxOffset, int outIxLen)
	{
		ids.add(instID);
		outIxOffs.put(instID, outIxOffset);
		outIxLens.put(instID, outIxLen);
	}

	public JobReturn constructJobReturn( long instID, JobReturn retAll )
	{
		//get output offset and len
		int off = outIxOffs.get(instID);
		int len = outIxLens.get(instID);
		
		//create partial output meta data 
		JobReturn ret = new JobReturn();
		ret.successful = retAll.successful;
		if( ret.successful ) {
			ret.metadata = new MetaData[len];
			System.arraycopy(retAll.metadata, off, ret.metadata, 0, len);
		}
		
		return ret;
	}
}

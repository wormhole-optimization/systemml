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

package org.apache.sysml.yarn.ropt;

import java.util.ArrayList;
import java.util.Collections;

import org.apache.sysml.parser.ForStatementBlock;
import org.apache.sysml.parser.IfStatementBlock;
import org.apache.sysml.parser.WhileStatementBlock;
import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.controlprogram.ForProgramBlock;
import org.apache.sysml.runtime.controlprogram.FunctionProgramBlock;
import org.apache.sysml.runtime.controlprogram.IfProgramBlock;
import org.apache.sysml.runtime.controlprogram.ProgramBlock;
import org.apache.sysml.runtime.controlprogram.WhileProgramBlock;

public class ResourceConfig 
{
	
	private long _cpres = -1;
	private ArrayList<Long> _mrres = null;
	
	public ResourceConfig( long cp, ArrayList<Long> mr )
	{
		_cpres = cp;
		_mrres = mr;
	}
	
	public ResourceConfig( ArrayList<ProgramBlock> prog, long init ) {
		//init cp memory
		_cpres = init;
		
		//init mr memory
		_mrres = new ArrayList<>();
		addProgramBlocks(prog, init);
	}
	
	public long getCPResource() {
		return (long)_cpres;
	}
	
	public void setCPResource( long res ) {
		_cpres = res;
	}


	public long getMRResources( int i ) {
		if( _mrres.size() <= i )
			throw new DMLRuntimeException("Memo table out-of-bounds: "+_mrres.size()+" vs "+i);
		return _mrres.get(i); 
	}

	public double[][] getMRResourcesMemo() {
		int len = _mrres.size();
		double[][] ret = new double[len][2];
		for( int i=0; i< len; i++ ){
			ret[i][0] = _mrres.get(i);
			ret[i][1] = -1;
		}
		return ret;
	}
	
	public void setMRResources( ArrayList<ProgramBlock> B, double[][] res ) {
		if( _mrres.size() != res.length )
			throw new DMLRuntimeException("Memo table sizes do not match: "+_mrres.size()+" vs "+res.length);
		int len = res.length;
		for( int i=0; i<len; i++ )
			_mrres.set(i, (long)res[i][0]);
	}

	public long getMaxMRResource() {
		double val = (double) Collections.max(_mrres);
		return (long)val;
	}
	
	public String serialize() 
	{
		StringBuilder ret = new StringBuilder();
		
		//serialize cp
		ret.append(YarnOptimizerUtils.toMB(_cpres));
		ret.append(",");
		
		//serialize mr
		int len = _mrres.size();
		for( int i=0; i<len-1; i++ ) {
			ret.append(YarnOptimizerUtils.toMB(_mrres.get(i)));
			ret.append(",");
		}
		ret.append(YarnOptimizerUtils.toMB(_mrres.get(len-1)));
		
		return ret.toString();
	}
	
	public static ResourceConfig deserialize( String str ) 
	{	
		String[] parts = str.split(",");
		
		//deserialize cp
		long cp = YarnOptimizerUtils.toB(Long.valueOf(parts[0]));
		
		//deserialize mr
		ArrayList<Long> mr = new ArrayList<>();
		for (int i=1; i<parts.length; i++) 
		{
			long val = YarnOptimizerUtils.toB(Long.parseLong(parts[i]));
			mr.add( val );
		}
		
		return new ResourceConfig(cp, mr);
	}

	private void addProgramBlocks( ArrayList<ProgramBlock> pbs, long init ) {
		for( ProgramBlock pb : pbs )
			addProgramBlock(pb, init);
	}

	private void addProgramBlock( ProgramBlock pb, long init ) 
	{
		if (pb instanceof FunctionProgramBlock)
		{
			FunctionProgramBlock fpb = (FunctionProgramBlock)pb;
			addProgramBlocks(fpb.getChildBlocks(), init);
		}
		else if (pb instanceof WhileProgramBlock)
		{
			WhileProgramBlock fpb = (WhileProgramBlock)pb;
			WhileStatementBlock wsb = (WhileStatementBlock)pb.getStatementBlock();
			if( ResourceOptimizer.INCLUDE_PREDICATES && wsb!=null && wsb.getPredicateHops()!=null )
				_mrres.add(init);		
			addProgramBlocks(fpb.getChildBlocks(), init);
		}	
		else if (pb instanceof IfProgramBlock)
		{
			IfProgramBlock fpb = (IfProgramBlock)pb;
			IfStatementBlock isb = (IfStatementBlock)pb.getStatementBlock();
			if( ResourceOptimizer.INCLUDE_PREDICATES && isb!=null && isb.getPredicateHops()!=null )
				_mrres.add(init);
			addProgramBlocks(fpb.getChildBlocksIfBody(), init);
			addProgramBlocks(fpb.getChildBlocksElseBody(), init);
		}
		else if (pb instanceof ForProgramBlock) //incl parfor
		{
			ForProgramBlock fpb = (ForProgramBlock)pb;
			ForStatementBlock fsb = (ForStatementBlock)pb.getStatementBlock();
			if( ResourceOptimizer.INCLUDE_PREDICATES && fsb!=null )
				_mrres.add(init);
			addProgramBlocks(fpb.getChildBlocks(), init);
		}
		else
		{
			//for objects hash is unique because memory location used
			_mrres.add(init);
		}
	}
}

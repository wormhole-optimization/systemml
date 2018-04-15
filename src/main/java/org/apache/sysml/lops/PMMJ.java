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

package org.apache.sysml.lops;

import org.apache.sysml.lops.LopProperties.ExecLocation;
import org.apache.sysml.lops.LopProperties.ExecType;
import org.apache.sysml.lops.compile.JobType;
import org.apache.sysml.parser.Expression.DataType;
import org.apache.sysml.parser.Expression.ValueType;

public class PMMJ extends Lop 
{
	
	public static final String OPCODE = "pmm";
	
	public enum CacheType {
		LEFT,
		LEFT_PART;
	}
	
	private CacheType _cacheType = null;
	private boolean _outputEmptyBlocks = true;
	private int _numThreads = 1;
	
	/**
	 * Constructor to setup a Permutation Matrix Multiplication
	 * 
	 * @param pminput permutation matrix input lop
	 * @param rightinput right lop
	 * @param nrow number of rows?
	 * @param dt data type
	 * @param vt value type
	 * @param partitioned true if partitioned
	 * @param emptyBlocks true if output empty blocks
	 * @param et execution type
	 */
	public PMMJ(Lop pminput, Lop rightinput, Lop nrow, DataType dt, ValueType vt, boolean partitioned, boolean emptyBlocks, ExecType et) {
		super(Lop.Type.PMMJ, dt, vt);
		addInput(pminput);
		addInput(rightinput);
		addInput(nrow);
		pminput.addOutput(this);
		rightinput.addOutput(this);
		nrow.addOutput(this);
		
		//setup mapmult parameters
		_cacheType = partitioned ? CacheType.LEFT_PART : CacheType.LEFT;
		_outputEmptyBlocks = emptyBlocks;
		
		boolean breaksAlignment = true;
		boolean aligner = false;
		boolean definesMRJob = false;
		ExecLocation el = (et == ExecType.MR) ? ExecLocation.Map : ExecLocation.ControlProgram;
		lps.addCompatibility(JobType.GMR);
		lps.addCompatibility(JobType.DATAGEN);
		lps.setProperties( inputs, et, el, breaksAlignment, aligner, definesMRJob );
	}

	@Override
	public String toString() {
		return "Operation = PMMJ";
	}
	
	@Override
	public String getInstructions(int input_index1, int input_index2, int input_index3, int output_index) {
		return getInstructions(String.valueOf(input_index1), String.valueOf(input_index2), 
				String.valueOf(input_index3), String.valueOf(output_index));
	}
	
	@Override
	public String getInstructions(String input_index1, String input_index2, String input_index3, String output_index) 
	{	
		StringBuilder sb = new StringBuilder();
		
		sb.append(getExecType());
		sb.append(Lop.OPERAND_DELIMITOR);
		
		sb.append(OPCODE);
		
		sb.append(Lop.OPERAND_DELIMITOR);
		sb.append( getInputs().get(0).prepInputOperand(input_index1));
		
		sb.append(Lop.OPERAND_DELIMITOR);
		sb.append( getInputs().get(1).prepInputOperand(input_index2));
		
		sb.append(Lop.OPERAND_DELIMITOR);
		if( getExecType() == ExecType.MR )
			sb.append( getInputs().get(2).prepScalarLabel() );
		else
			sb.append( getInputs().get(2).prepInputOperand(input_index3));
		
		sb.append(Lop.OPERAND_DELIMITOR);
		sb.append( prepOutputOperand(output_index));
		
		if( getExecType() == ExecType.SPARK ) {
			sb.append(Lop.OPERAND_DELIMITOR);
			sb.append(_cacheType);
		}
		else if( getExecType() == ExecType.MR ) {
			sb.append(Lop.OPERAND_DELIMITOR);
			sb.append(_cacheType);
			sb.append(Lop.OPERAND_DELIMITOR);
			sb.append(_outputEmptyBlocks);
		}
		else if( getExecType() == ExecType.CP ) {
			sb.append( OPERAND_DELIMITOR );
			sb.append( _numThreads );
		}
		
		return sb.toString();
	}

	@Override
	public boolean usesDistributedCache() {
		return true;
	}
	
	@Override
	public int[] distributedCacheInputIndex() {	
		return new int[]{1};
	}
	
	public void setNumThreads(int k) {
		_numThreads = k;
	}
}

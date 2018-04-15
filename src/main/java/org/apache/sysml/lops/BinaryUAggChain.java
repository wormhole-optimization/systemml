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


public class BinaryUAggChain extends Lop 
{
	
	public static final String OPCODE = "binuaggchain";

	//outer operation
	private Binary.OperationTypes _binOp             = null;	
	//inner operation
	private Aggregate.OperationTypes _uaggOp         = null;
	private PartialAggregate.DirectionTypes _uaggDir = null;
	
	
	/**
	 * Constructor to setup a map mult chain without weights
	 * 
	 * 
	 * @param input1 low-level operator
	 * @param bop binary operation type
	 * @param uaop aggregate operation type
	 * @param uadir partial aggregate direction type
	 * @param dt data type
	 * @param vt value type
	 * @param et execution type
	 */
	public BinaryUAggChain(Lop input1, Binary.OperationTypes bop, Aggregate.OperationTypes uaop, PartialAggregate.DirectionTypes uadir, DataType dt, ValueType vt, ExecType et) {
		super(Lop.Type.BinUaggChain, dt, vt);
		addInput(input1); //X
		input1.addOutput(this); 
		
		//setup operator types
		_binOp = bop;
		_uaggOp = uaop;
		_uaggDir = uadir;
		
		//setup MR parameters 
		if( et == ExecType.MR )
		{
			boolean breaksAlignment = false;
			boolean aligner = false;
			boolean definesMRJob = false;
			lps.addCompatibility(JobType.GMR);
			lps.addCompatibility(JobType.DATAGEN);
			lps.addCompatibility(JobType.REBLOCK);
			lps.addCompatibility(JobType.CSV_REBLOCK);
			lps.addCompatibility(JobType.MMCJ);
			lps.addCompatibility(JobType.MMRJ);
			lps.setProperties( inputs, ExecType.MR, ExecLocation.MapOrReduce, breaksAlignment, aligner, definesMRJob );
		}
		else //SPARK
		{
			boolean breaksAlignment = false;
			boolean aligner = false;
			boolean definesMRJob = false;
			lps.addCompatibility(JobType.INVALID);
			lps.setProperties(inputs, et, ExecLocation.ControlProgram, breaksAlignment, aligner, definesMRJob);
		}
	}
	
	@Override
	public String toString() {
		return "Operation = BinUaggChain";
	}
	
	@Override
	public String getInstructions(int input_index1, int output_index) {
		return getInstructions(
				String.valueOf(input_index1), 
				String.valueOf(output_index));
	}
	
	@Override
	public String getInstructions(String input1, String output)
	{
		StringBuilder sb = new StringBuilder();
		
		//exec type
		sb.append(getExecType());
		sb.append(Lop.OPERAND_DELIMITOR);
		
		//inst op code
		sb.append(OPCODE);
		sb.append(Lop.OPERAND_DELIMITOR);

		//outer operation op code
		sb.append(Binary.getOpcode(_binOp));
		sb.append(Lop.OPERAND_DELIMITOR);
		
		//inner operation op code
		sb.append(PartialAggregate.getOpcode(_uaggOp, _uaggDir));		
		sb.append(Lop.OPERAND_DELIMITOR);

		//inputs and outputs
		sb.append( getInputs().get(0).prepInputOperand(input1));
		sb.append(Lop.OPERAND_DELIMITOR);
		sb.append( this.prepOutputOperand(output));
				
		return sb.toString();
	}
}

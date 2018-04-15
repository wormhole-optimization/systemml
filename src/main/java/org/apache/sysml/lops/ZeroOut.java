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

public class ZeroOut  extends Lop 
{

	
	private void init(Lop inputMatrix, Lop rowL, Lop rowU, Lop colL, Lop colU, long rowDim, long colDim, DataType dt, ValueType vt, ExecType et) {
		this.addInput(inputMatrix);
		this.addInput(rowL);
		this.addInput(rowU);
		this.addInput(colL);
		this.addInput(colU);
		
		inputMatrix.addOutput(this);		
		rowL.addOutput(this);
		rowU.addOutput(this);
		colL.addOutput(this);
		colU.addOutput(this);

		boolean breaksAlignment = true;
		boolean aligner = false;
		boolean definesMRJob = false;
		
		if ( et == ExecType.MR ) {
			
			lps.addCompatibility(JobType.GMR);
			lps.addCompatibility(JobType.DATAGEN);
			lps.addCompatibility(JobType.MMCJ);
			lps.addCompatibility(JobType.MMRJ);
			this.lps.setProperties(inputs, et, ExecLocation.Map, breaksAlignment, aligner, definesMRJob);
		} 
		else {
			lps.addCompatibility(JobType.INVALID);
			this.lps.setProperties(inputs, et, ExecLocation.ControlProgram, breaksAlignment, aligner, definesMRJob);
		}
	}

	public ZeroOut(Lop input, Lop rowL, Lop rowU, Lop colL, Lop colU, long rowDim,
		long colDim, DataType dt, ValueType vt, ExecType et) {
		super(Lop.Type.ZeroOut, dt, vt);
		init(input, rowL, rowU, colL, colU, rowDim, colDim, dt, vt, et);
	}
	
	private static String getOpcode() {
		return "zeroOut";
	}
	
	@Override
	public String getInstructions(String input, String rowl, String rowu, String coll, String colu, String output) {
		StringBuilder sb = new StringBuilder();
		sb.append( getExecType() );
		sb.append( OPERAND_DELIMITOR );
		sb.append( getOpcode() );
		sb.append( OPERAND_DELIMITOR );
		sb.append( getInputs().get(0).prepInputOperand(input));
		sb.append( OPERAND_DELIMITOR ); 
		
		// rowl, rowu
		sb.append( getInputs().get(1).prepScalarInputOperand(getExecType()));
		sb.append( OPERAND_DELIMITOR );
		sb.append( getInputs().get(2).prepScalarInputOperand(getExecType()));
		sb.append( OPERAND_DELIMITOR );
				
		// coll, colu
		sb.append( getInputs().get(3).prepScalarInputOperand(getExecType()));
		sb.append( OPERAND_DELIMITOR );
		sb.append( getInputs().get(4).prepScalarInputOperand(getExecType()));
		sb.append( OPERAND_DELIMITOR );
		
		sb.append( this.prepOutputOperand(output));
		
		return sb.toString();
	}

	@Override
	public String getInstructions(int input_index1, int input_index2, int input_index3, int input_index4, int input_index5, int output_index) {
		return getInstructions(
			String.valueOf(input_index1), String.valueOf(input_index2), 
			String.valueOf(input_index3), String.valueOf(input_index4), 
			String.valueOf(input_index5), String.valueOf(output_index));
	}

	@Override
	public String toString() {
		return "ZeroOut";
	}
}

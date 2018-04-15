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
import org.apache.sysml.parser.Expression.*;


/**
 * Lop to perform binary operation. Both inputs must be matrices or vectors. 
 * Example - A = B + C, where B and C are matrices or vectors.
 */

public class Binary extends Lop 
{
	public enum OperationTypes {
		ADD, SUBTRACT, MULTIPLY, DIVIDE, MINUS1_MULTIPLY, MODULUS, INTDIV, MATMULT, 
		LESS_THAN, LESS_THAN_OR_EQUALS, GREATER_THAN, GREATER_THAN_OR_EQUALS, EQUALS, NOT_EQUALS,
		AND, OR, XOR,
		MAX, MIN, POW, SOLVE, NOTSUPPORTED,
		BW_AND, BW_OR, BW_XOR, BW_SHIFTL, BW_SHIFTR, //Bitwise operations
	}

	private OperationTypes operation;
	private int numThreads = -1;
	boolean isLeftTransposed; boolean isRightTransposed; // Used for GPU matmult operation
	
	/**
	 * Constructor to perform a binary operation.
	 * 
	 * @param input1 low-level operator 1
	 * @param input2 low-level operator 2
	 * @param op operation type
	 * @param dt data type
	 * @param vt value type
	 * @param et exec type
	 */
	public Binary(Lop input1, Lop input2, OperationTypes op, DataType dt, ValueType vt, ExecType et) {
		this(input1, input2, op, dt, vt, et, 1);
	}
	
	public Binary(Lop input1, Lop input2, OperationTypes op, DataType dt, ValueType vt, ExecType et, int k) {
		super(Lop.Type.Binary, dt, vt);
		init(input1, input2, op, dt, vt, et);	
		numThreads = k;
	}
	
	public Binary(Lop input1, Lop input2, OperationTypes op, DataType dt, ValueType vt, ExecType et, 
			boolean isLeftTransposed, boolean isRightTransposed) {
		super(Lop.Type.Binary, dt, vt);
		init(input1, input2, op, dt, vt, et);
		this.isLeftTransposed = isLeftTransposed;
		this.isRightTransposed = isRightTransposed;
	}
	
	private void init(Lop input1, Lop input2, OperationTypes op, DataType dt, ValueType vt, ExecType et) 
	{
		operation = op;
		this.addInput(input1);
		this.addInput(input2);
		input1.addOutput(this);
		input2.addOutput(this);
		
		boolean breaksAlignment = false;
		boolean aligner = false;
		boolean definesMRJob = false;
		
		if ( et == ExecType.MR ) {
			lps.addCompatibility(JobType.GMR);
			lps.addCompatibility(JobType.DATAGEN);
			lps.addCompatibility(JobType.REBLOCK);
			this.lps.setProperties( inputs, et, ExecLocation.Reduce, breaksAlignment, aligner, definesMRJob );
		}
		else if ( et == ExecType.CP || et == ExecType.SPARK || et == ExecType.GPU ){
			lps.addCompatibility(JobType.INVALID);
			this.lps.setProperties( inputs, et, ExecLocation.ControlProgram, breaksAlignment, aligner, definesMRJob );
		}
	}

	@Override
	public String toString() {
	
		return " Operation: " + operation;

	}

	/**
	 * method to get operation type
	 * @return operation type
	 */
	 
	public OperationTypes getOperationType()
	{
		return operation;
	}

	private String getOpcode()
	{
		return getOpcode( operation );
	}
	
	public static String getOpcode( OperationTypes op ) {
		switch(op) {
		/* Arithmetic */
		case ADD:
			return "+";
		case SUBTRACT:
			return "-";
		case MULTIPLY:
			return "*";
		case DIVIDE:
			return "/";
		case MODULUS:
			return "%%";	
		case INTDIV:
			return "%/%";		
		case MATMULT:
			return "ba+*";
		case MINUS1_MULTIPLY:
			return "1-*";
		
		/* Relational */
		case LESS_THAN:
			return "<";
		case LESS_THAN_OR_EQUALS:
			return "<=";
		case GREATER_THAN:
			return ">";
		case GREATER_THAN_OR_EQUALS:
			return ">=";
		case EQUALS:
			return "==";
		case NOT_EQUALS:
			return "!=";
		
		/* Boolean */
		case AND:
			return "&&";
		case OR:
			return "||";

		/* Binary Builtin Function */
		case XOR:
			return "xor";
		case BW_AND:
			return "bitwAnd";
		case BW_OR:
			return "bitwOr";
		case BW_XOR:
			return "bitwXor";
		case BW_SHIFTL:
			return "bitwShiftL";
		case BW_SHIFTR:
			return "bitwShiftR";

		/* Builtin Functions */
		case MIN:
			return "min";
		case MAX:
			return "max";
		case POW:
			return "^";
			
		case SOLVE:
			return "solve";
			
		default:
			throw new UnsupportedOperationException("Instruction is not defined for Binary operation: " + op);
		}
	}
	
	
	@Override
	public String getInstructions(int input_index1, int input_index2, int output_index) {
		return getInstructions(
				String.valueOf(input_index1), 
				String.valueOf(input_index2), 
				String.valueOf(output_index));
	}
	
	@Override
	public String getInstructions(String input1, String input2, String output) {
		StringBuilder sb = new StringBuilder();
		sb.append( getExecType() );
		sb.append( OPERAND_DELIMITOR );
		sb.append( getOpcode() );
		sb.append( OPERAND_DELIMITOR );
		
		sb.append ( getInputs().get(0).prepInputOperand(input1));
		sb.append( OPERAND_DELIMITOR );
		
		sb.append ( getInputs().get(1).prepInputOperand(input2));
		sb.append( OPERAND_DELIMITOR );
		
		sb.append( this.prepOutputOperand(output));
		
		//append degree of parallelism for matrix multiplications
		if( operation == OperationTypes.MATMULT && getExecType()==ExecType.CP ) {
			sb.append( OPERAND_DELIMITOR );
			sb.append( numThreads );
		}
		else if( operation == OperationTypes.MATMULT && getExecType()==ExecType.GPU ) {
			sb.append( OPERAND_DELIMITOR );
			sb.append( isLeftTransposed );
			sb.append( OPERAND_DELIMITOR );
			sb.append( isRightTransposed );
		}
		
		return sb.toString();
	}
}
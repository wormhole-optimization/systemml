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

package org.apache.sysml.runtime.instructions.cp;

import org.apache.sysml.lops.Ctable;
import org.apache.sysml.parser.Expression.DataType;
import org.apache.sysml.parser.Expression.ValueType;
import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.controlprogram.context.ExecutionContext;
import org.apache.sysml.runtime.instructions.Instruction;
import org.apache.sysml.runtime.instructions.InstructionUtils;
import org.apache.sysml.runtime.matrix.data.CTableMap;
import org.apache.sysml.runtime.matrix.data.MatrixBlock;
import org.apache.sysml.runtime.matrix.operators.SimpleOperator;
import org.apache.sysml.runtime.util.DataConverter;
import org.apache.sysml.runtime.util.LongLongDoubleHashMap.EntryType;

public class CtableCPInstruction extends ComputationCPInstruction {
	private final String _outDim1;
	private final String _outDim2;
	private final boolean _dim1Literal;
	private final boolean _dim2Literal;
	private final boolean _isExpand;
	private final boolean _ignoreZeros;

	private CtableCPInstruction(CPOperand in1, CPOperand in2, CPOperand in3, CPOperand out,
			String outputDim1, boolean dim1Literal, String outputDim2, boolean dim2Literal, boolean isExpand,
			boolean ignoreZeros, String opcode, String istr) {
		super(CPType.Ctable, null, in1, in2, in3, out, opcode, istr);
		_outDim1 = outputDim1;
		_dim1Literal = dim1Literal;
		_outDim2 = outputDim2;
		_dim2Literal = dim2Literal;
		_isExpand = isExpand;
		_ignoreZeros = ignoreZeros;
	}

	public static CtableCPInstruction parseInstruction(String inst)
	{
		String[] parts = InstructionUtils.getInstructionPartsWithValueType(inst);
		InstructionUtils.checkNumFields ( parts, 7 );
		
		String opcode = parts[0];
		
		//handle opcode
		if ( !(opcode.equalsIgnoreCase("ctable") || opcode.equalsIgnoreCase("ctableexpand")) ) {
			throw new DMLRuntimeException("Unexpected opcode in TertiaryCPInstruction: " + inst);
		}
		boolean isExpand = opcode.equalsIgnoreCase("ctableexpand");
		
		//handle operands
		CPOperand in1 = new CPOperand(parts[1]);
		CPOperand in2 = new CPOperand(parts[2]);
		CPOperand in3 = new CPOperand(parts[3]);
		
		//handle known dimension information
		String[] dim1Fields = parts[4].split(Instruction.LITERAL_PREFIX);
		String[] dim2Fields = parts[5].split(Instruction.LITERAL_PREFIX);

		CPOperand out = new CPOperand(parts[6]);
		boolean ignoreZeros = Boolean.parseBoolean(parts[7]);
		
		// ctable does not require any operator, so we simply pass-in a dummy operator with null functionobject
		return new CtableCPInstruction(in1, in2, in3, out, dim1Fields[0], Boolean.parseBoolean(dim1Fields[1]), dim2Fields[0], Boolean.parseBoolean(dim2Fields[1]), isExpand, ignoreZeros, opcode, inst);
	}

	private Ctable.OperationTypes findCtableOperation() {
		DataType dt1 = input1.getDataType();
		DataType dt2 = input2.getDataType();
		DataType dt3 = input3.getDataType();
		return Ctable.findCtableOperationByInputDataTypes(dt1, dt2, dt3);
	}
	
	@Override
	public void processInstruction(ExecutionContext ec) {
		MatrixBlock matBlock1 = ec.getMatrixInput(input1.getName(), getExtendedOpcode());
		MatrixBlock matBlock2=null, wtBlock=null;
		double cst1, cst2;
		
		CTableMap resultMap = new CTableMap(EntryType.INT);
		MatrixBlock resultBlock = null;
		Ctable.OperationTypes ctableOp = findCtableOperation();
		ctableOp = _isExpand ? Ctable.OperationTypes.CTABLE_EXPAND_SCALAR_WEIGHT : ctableOp;
		
		long outputDim1 = (_dim1Literal ? (long) Double.parseDouble(_outDim1) : (ec.getScalarInput(_outDim1, ValueType.DOUBLE, false)).getLongValue());
		long outputDim2 = (_dim2Literal ? (long) Double.parseDouble(_outDim2) : (ec.getScalarInput(_outDim2, ValueType.DOUBLE, false)).getLongValue());
		
		boolean outputDimsKnown = (outputDim1 != -1 && outputDim2 != -1);
		if ( outputDimsKnown ) {
			int inputRows = matBlock1.getNumRows();
			int inputCols = matBlock1.getNumColumns();
			boolean sparse = MatrixBlock.evalSparseFormatInMemory(outputDim1, outputDim2, inputRows*inputCols);
			//only create result block if dense; it is important not to aggregate on sparse result
			//blocks because it would implicitly turn the O(N) algorithm into O(N log N). 
			if( !sparse )
				resultBlock = new MatrixBlock((int)outputDim1, (int)outputDim2, false); 
		}
		if( _isExpand ){
			resultBlock = new MatrixBlock( matBlock1.getNumRows(), Integer.MAX_VALUE, true );
		}
		
		switch(ctableOp) {
			case CTABLE_TRANSFORM: //(VECTOR)
				// F=ctable(A,B,W)
				matBlock2 = ec.getMatrixInput(input2.getName(), getExtendedOpcode());
				wtBlock = ec.getMatrixInput(input3.getName(), getExtendedOpcode());
				matBlock1.ctableOperations((SimpleOperator)_optr, matBlock2, wtBlock, resultMap, resultBlock);
				break;
			case CTABLE_TRANSFORM_SCALAR_WEIGHT: //(VECTOR/MATRIX)
				// F = ctable(A,B) or F = ctable(A,B,1)
				matBlock2 = ec.getMatrixInput(input2.getName(), getExtendedOpcode());
				cst1 = ec.getScalarInput(input3.getName(), input3.getValueType(), input3.isLiteral()).getDoubleValue();
				matBlock1.ctableOperations((SimpleOperator)_optr, matBlock2, cst1, _ignoreZeros, resultMap, resultBlock);
				break;
			case CTABLE_EXPAND_SCALAR_WEIGHT: //(VECTOR)
				// F = ctable(seq,A) or F = ctable(seq,B,1)
				matBlock2 = ec.getMatrixInput(input2.getName(), getExtendedOpcode());
				cst1 = ec.getScalarInput(input3.getName(), input3.getValueType(), input3.isLiteral()).getDoubleValue();
				// only resultBlock.rlen known, resultBlock.clen set in operation
				matBlock1.ctableOperations((SimpleOperator)_optr, matBlock2, cst1, resultBlock);
				break;
			case CTABLE_TRANSFORM_HISTOGRAM: //(VECTOR)
				// F=ctable(A,1) or F = ctable(A,1,1)
				cst1 = ec.getScalarInput(input2.getName(), input2.getValueType(), input2.isLiteral()).getDoubleValue();
				cst2 = ec.getScalarInput(input3.getName(), input3.getValueType(), input3.isLiteral()).getDoubleValue();
				matBlock1.ctableOperations((SimpleOperator)_optr, cst1, cst2, resultMap, resultBlock);
				break;
			case CTABLE_TRANSFORM_WEIGHTED_HISTOGRAM: //(VECTOR)
				// F=ctable(A,1,W)
				wtBlock = ec.getMatrixInput(input3.getName(), getExtendedOpcode());
				cst1 = ec.getScalarInput(input2.getName(), input2.getValueType(), input2.isLiteral()).getDoubleValue();
				matBlock1.ctableOperations((SimpleOperator)_optr, cst1, wtBlock, resultMap, resultBlock);
				break;
			
			default:
				throw new DMLRuntimeException("Encountered an invalid ctable operation ("+ctableOp+") while executing instruction: " + this.toString());
		}
		
		if(input1.getDataType() == DataType.MATRIX)
			ec.releaseMatrixInput(input1.getName(), getExtendedOpcode());
		if(input2.getDataType() == DataType.MATRIX)
			ec.releaseMatrixInput(input2.getName(), getExtendedOpcode());
		if(input3.getDataType() == DataType.MATRIX)
			ec.releaseMatrixInput(input3.getName(), getExtendedOpcode());
		
		if ( resultBlock == null ){
			//we need to respect potentially specified output dimensions here, because we might have 
			//decided for hash-aggregation just to prevent inefficiency in case of sparse outputs.  
			if( outputDimsKnown )
				resultBlock = DataConverter.convertToMatrixBlock( resultMap, (int)outputDim1, (int)outputDim2 );
			else
				resultBlock = DataConverter.convertToMatrixBlock( resultMap );
		}
		else
			resultBlock.examSparsity();
		
		// Ensure right dense/sparse output representation for special cases
		// such as ctable expand (guarded by released input memory)
		if( checkGuardedRepresentationChange(matBlock1, matBlock2, resultBlock) ) {
			resultBlock.examSparsity();
		}
		
		ec.setMatrixOutput(output.getName(), resultBlock, getExtendedOpcode());
	}
}

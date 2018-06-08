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

package org.apache.sysml.runtime.instructions;

import java.util.StringTokenizer;

import org.apache.sysml.lops.AppendM;
import org.apache.sysml.lops.BinaryM;
import org.apache.sysml.lops.GroupedAggregateM;
import org.apache.sysml.lops.LopProperties.ExecType;
import org.apache.sysml.lops.MapMult;
import org.apache.sysml.lops.MapMultChain;
import org.apache.sysml.lops.PMMJ;
import org.apache.sysml.lops.PartialAggregate.CorrectionLocationType;
import org.apache.sysml.lops.UAggOuterChain;
import org.apache.sysml.lops.WeightedCrossEntropy;
import org.apache.sysml.lops.WeightedCrossEntropyR;
import org.apache.sysml.lops.WeightedDivMM;
import org.apache.sysml.lops.WeightedDivMMR;
import org.apache.sysml.lops.WeightedSigmoid;
import org.apache.sysml.lops.WeightedSigmoidR;
import org.apache.sysml.lops.WeightedSquaredLoss;
import org.apache.sysml.lops.WeightedSquaredLossR;
import org.apache.sysml.lops.WeightedUnaryMM;
import org.apache.sysml.lops.WeightedUnaryMMR;
import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.functionobjects.And;
import org.apache.sysml.runtime.functionobjects.BitwAnd;
import org.apache.sysml.runtime.functionobjects.BitwOr;
import org.apache.sysml.runtime.functionobjects.BitwShiftL;
import org.apache.sysml.runtime.functionobjects.BitwShiftR;
import org.apache.sysml.runtime.functionobjects.BitwXor;
import org.apache.sysml.runtime.functionobjects.Builtin;
import org.apache.sysml.runtime.functionobjects.Builtin.BuiltinCode;
import org.apache.sysml.runtime.functionobjects.CM;
import org.apache.sysml.runtime.functionobjects.Divide;
import org.apache.sysml.runtime.functionobjects.Equals;
import org.apache.sysml.runtime.functionobjects.GreaterThan;
import org.apache.sysml.runtime.functionobjects.GreaterThanEquals;
import org.apache.sysml.runtime.functionobjects.IfElse;
import org.apache.sysml.runtime.functionobjects.IndexFunction;
import org.apache.sysml.runtime.functionobjects.IntegerDivide;
import org.apache.sysml.runtime.functionobjects.KahanPlus;
import org.apache.sysml.runtime.functionobjects.KahanPlusSq;
import org.apache.sysml.runtime.functionobjects.LessThan;
import org.apache.sysml.runtime.functionobjects.LessThanEquals;
import org.apache.sysml.runtime.functionobjects.Mean;
import org.apache.sysml.runtime.functionobjects.Minus;
import org.apache.sysml.runtime.functionobjects.Minus1Multiply;
import org.apache.sysml.runtime.functionobjects.MinusMultiply;
import org.apache.sysml.runtime.functionobjects.MinusNz;
import org.apache.sysml.runtime.functionobjects.Modulus;
import org.apache.sysml.runtime.functionobjects.Multiply;
import org.apache.sysml.runtime.functionobjects.Multiply2;
import org.apache.sysml.runtime.functionobjects.Not;
import org.apache.sysml.runtime.functionobjects.NotEquals;
import org.apache.sysml.runtime.functionobjects.Or;
import org.apache.sysml.runtime.functionobjects.Plus;
import org.apache.sysml.runtime.functionobjects.PlusMultiply;
import org.apache.sysml.runtime.functionobjects.Power;
import org.apache.sysml.runtime.functionobjects.Power2;
import org.apache.sysml.runtime.functionobjects.ReduceAll;
import org.apache.sysml.runtime.functionobjects.ReduceCol;
import org.apache.sysml.runtime.functionobjects.ReduceDiag;
import org.apache.sysml.runtime.functionobjects.ReduceRow;
import org.apache.sysml.runtime.functionobjects.Xor;
import org.apache.sysml.runtime.instructions.cp.CPInstruction.CPType;
import org.apache.sysml.runtime.instructions.cp.CPOperand;
import org.apache.sysml.runtime.instructions.gpu.GPUInstruction.GPUINSTRUCTION_TYPE;
import org.apache.sysml.runtime.instructions.mr.MRInstruction.MRType;
import org.apache.sysml.runtime.instructions.spark.SPInstruction.SPType;
import org.apache.sysml.runtime.matrix.data.LibCommonsMath;
import org.apache.sysml.runtime.matrix.operators.AggregateBinaryOperator;
import org.apache.sysml.runtime.matrix.operators.AggregateOperator;
import org.apache.sysml.runtime.matrix.operators.AggregateTernaryOperator;
import org.apache.sysml.runtime.matrix.operators.AggregateUnaryOperator;
import org.apache.sysml.runtime.matrix.operators.BinaryOperator;
import org.apache.sysml.runtime.matrix.operators.CMOperator.AggregateOperationTypes;
import org.apache.sysml.runtime.matrix.operators.LeftScalarOperator;
import org.apache.sysml.runtime.matrix.operators.Operator;
import org.apache.sysml.runtime.matrix.operators.RightScalarOperator;
import org.apache.sysml.runtime.matrix.operators.ScalarOperator;
import org.apache.sysml.runtime.matrix.operators.TernaryOperator;
import org.apache.sysml.runtime.matrix.operators.UnaryOperator;


public class InstructionUtils 
{

	public static int checkNumFields( String str, int expected ) {
		//note: split required for empty tokens
		int numParts = str.split(Instruction.OPERAND_DELIM).length;
		int numFields = numParts - 2; // -2 accounts for execType and opcode
		
		if ( numFields != expected ) 
			throw new DMLRuntimeException("checkNumFields() for (" + str + ") -- expected number (" + expected + ") != is not equal to actual number (" + numFields + ").");
		
		return numFields; 
	}

	public static int checkNumFields( String[] parts, int expected ) {
		int numParts = parts.length;
		int numFields = numParts - 1; //account for opcode
		
		if ( numFields != expected ) 
			throw new DMLRuntimeException("checkNumFields() -- expected number (" + expected + ") != is not equal to actual number (" + numFields + ").");
		
		return numFields; 
	}

	public static int checkNumFields( String[] parts, int expected1, int expected2 ) {
		int numParts = parts.length;
		int numFields = numParts - 1; //account for opcode
		
		if ( numFields != expected1 && numFields != expected2 ) 
			throw new DMLRuntimeException("checkNumFields() -- expected number (" + expected1 + " or "+ expected2 +") != is not equal to actual number (" + numFields + ").");
		
		return numFields; 
	}

	public static int checkNumFields( String str, int expected1, int expected2 ) {
		//note: split required for empty tokens
		int numParts = str.split(Instruction.OPERAND_DELIM).length;
		int numFields = numParts - 2; // -2 accounts for execType and opcode
		if ( numFields != expected1 && numFields != expected2 ) 
			throw new DMLRuntimeException("checkNumFields() for (" + str + ") -- expected number (" + expected1 + " or "+ expected2 +") != is not equal to actual number (" + numFields + ").");
		return numFields; 
	}
	
	/**
	 * Given an instruction string, strip-off the execution type and return 
	 * opcode and all input/output operands WITHOUT their data/value type. 
	 * i.e., ret.length = parts.length-1 (-1 for execution type)
	 * 
	 * @param str instruction string
	 * @return instruction parts as string array
	 */
	public static String[] getInstructionParts( String str ) {
		StringTokenizer st = new StringTokenizer( str, Instruction.OPERAND_DELIM );
		String[] ret = new String[st.countTokens()-1];
		st.nextToken(); // stripping-off the exectype
		ret[0] = st.nextToken(); // opcode
		int index = 1;
		while( st.hasMoreTokens() ){
			String tmp = st.nextToken();
			int ix = tmp.indexOf(Instruction.DATATYPE_PREFIX);
			ret[index++] = tmp.substring(0,((ix>=0)?ix:tmp.length()));	
		}
		return ret;
	}
	
	/**
	 * Given an instruction string, this function strips-off the 
	 * execution type (CP or MR) and returns the remaining parts, 
	 * which include the opcode as well as the input and output operands.
	 * Each returned part will have the datatype and valuetype associated
	 * with the operand.
	 * 
	 * This function is invoked mainly for parsing CPInstructions.
	 * 
	 * @param str instruction string
	 * @return instruction parts as string array
	 */
	public static String[] getInstructionPartsWithValueType( String str ) {
		//note: split required for empty tokens
		String[] parts = str.split(Instruction.OPERAND_DELIM, -1);
		String[] ret = new String[parts.length-1]; // stripping-off the exectype
		ret[0] = parts[1]; // opcode
		for( int i=1; i<parts.length; i++ )
			ret[i-1] = parts[i];
		
		return ret;
	}
	
	public static ExecType getExecType( String str ) {
		int ix = str.indexOf(Instruction.OPERAND_DELIM);
		return ExecType.valueOf(str.substring(0, ix));
	}

	public static String getOpCode( String str ) {
		int ix1 = str.indexOf(Instruction.OPERAND_DELIM);
		int ix2 = str.indexOf(Instruction.OPERAND_DELIM, ix1+1);
		return str.substring(ix1+1, ix2);
	}

	public static MRType getMRType( String str ) {
		return MRInstructionParser.String2MRInstructionType.get( getOpCode(str) ); 
	}

	public static SPType getSPType( String str ) {
		return SPInstructionParser.String2SPInstructionType.get( getOpCode(str) ); 
	}

	public static CPType getCPType( String str ) {
		return CPInstructionParser.String2CPInstructionType.get( getOpCode(str) ); 
	}

	public static GPUINSTRUCTION_TYPE getGPUType( String str ) {
		return GPUInstructionParser.String2GPUInstructionType.get( getOpCode(str) ); 
	}

	public static boolean isBuiltinFunction( String opcode ) {
		Builtin.BuiltinCode bfc = Builtin.String2BuiltinCode.get(opcode);
		return (bfc != null);
	}

	/**
	 * Evaluates if at least one instruction of the given instruction set
	 * used the distributed cache; this call can also be used for individual
	 * instructions. 
	 * 
	 * @param str instruction set
	 * @return true if at least one instruction uses distributed cache
	 */
	public static boolean isDistributedCacheUsed(String str) 
	{	
		String[] parts = str.split(Instruction.INSTRUCTION_DELIM);
		for(String inst : parts) 
		{
			String opcode = getOpCode(inst);
			if(  opcode.equalsIgnoreCase(AppendM.OPCODE)  
			   || opcode.equalsIgnoreCase(MapMult.OPCODE)
			   || opcode.equalsIgnoreCase(MapMultChain.OPCODE)
			   || opcode.equalsIgnoreCase(PMMJ.OPCODE)
			   || opcode.equalsIgnoreCase(UAggOuterChain.OPCODE)
			   || opcode.equalsIgnoreCase(GroupedAggregateM.OPCODE)
			   || isDistQuaternaryOpcode( opcode ) //multiple quaternary opcodes
			   || BinaryM.isOpcode( opcode ) ) //multiple binary opcodes	
			{
				return true;
			}
		}
		return false;
	}

	public static AggregateUnaryOperator parseBasicAggregateUnaryOperator(String opcode) {
		return parseBasicAggregateUnaryOperator(opcode, 1);
	}
	
	public static AggregateUnaryOperator parseBasicAggregateUnaryOperator(String opcode, int numThreads)
	{
		AggregateUnaryOperator aggun = null;
		
		if ( opcode.equalsIgnoreCase("uak+") ) {
			AggregateOperator agg = new AggregateOperator(0, KahanPlus.getKahanPlusFnObject(), true, CorrectionLocationType.LASTCOLUMN);
			aggun = new AggregateUnaryOperator(agg, ReduceAll.getReduceAllFnObject(), numThreads);
		}
		else if ( opcode.equalsIgnoreCase("uark+") ) { // RowSums
			AggregateOperator agg = new AggregateOperator(0, KahanPlus.getKahanPlusFnObject(), true, CorrectionLocationType.LASTCOLUMN);
			aggun = new AggregateUnaryOperator(agg, ReduceCol.getReduceColFnObject(), numThreads);
		} 
		else if ( opcode.equalsIgnoreCase("uack+") ) { // ColSums
			AggregateOperator agg = new AggregateOperator(0, KahanPlus.getKahanPlusFnObject(), true, CorrectionLocationType.LASTROW);
			aggun = new AggregateUnaryOperator(agg, ReduceRow.getReduceRowFnObject(), numThreads);
		}
		else if ( opcode.equalsIgnoreCase("uasqk+") ) {
			AggregateOperator agg = new AggregateOperator(0, KahanPlusSq.getKahanPlusSqFnObject(), true, CorrectionLocationType.LASTCOLUMN);
			aggun = new AggregateUnaryOperator(agg, ReduceAll.getReduceAllFnObject(), numThreads);
		}
		else if ( opcode.equalsIgnoreCase("uarsqk+") ) {
			// RowSums
			AggregateOperator agg = new AggregateOperator(0, KahanPlusSq.getKahanPlusSqFnObject(), true, CorrectionLocationType.LASTCOLUMN);
			aggun = new AggregateUnaryOperator(agg, ReduceCol.getReduceColFnObject(), numThreads);
		}
		else if ( opcode.equalsIgnoreCase("uacsqk+") ) {
			// ColSums
			AggregateOperator agg = new AggregateOperator(0, KahanPlusSq.getKahanPlusSqFnObject(), true, CorrectionLocationType.LASTROW);
			aggun = new AggregateUnaryOperator(agg, ReduceRow.getReduceRowFnObject(), numThreads);
		}
		else if ( opcode.equalsIgnoreCase("uamean") ) {
			// Mean
			AggregateOperator agg = new AggregateOperator(0, Mean.getMeanFnObject(), true, CorrectionLocationType.LASTTWOCOLUMNS);
			aggun = new AggregateUnaryOperator(agg, ReduceAll.getReduceAllFnObject(), numThreads);
		} 
		else if ( opcode.equalsIgnoreCase("uarmean") ) {
			// RowMeans
			AggregateOperator agg = new AggregateOperator(0, Mean.getMeanFnObject(), true, CorrectionLocationType.LASTTWOCOLUMNS);
			aggun = new AggregateUnaryOperator(agg, ReduceCol.getReduceColFnObject(), numThreads);
		} 
		else if ( opcode.equalsIgnoreCase("uacmean") ) {
			// ColMeans
			AggregateOperator agg = new AggregateOperator(0, Mean.getMeanFnObject(), true, CorrectionLocationType.LASTTWOROWS);
			aggun = new AggregateUnaryOperator(agg, ReduceRow.getReduceRowFnObject(), numThreads);
		}
		else if ( opcode.equalsIgnoreCase("uavar") ) {
			// Variance
			CM varFn = CM.getCMFnObject(AggregateOperationTypes.VARIANCE);
			CorrectionLocationType cloc = CorrectionLocationType.LASTFOURCOLUMNS;
			AggregateOperator agg = new AggregateOperator(0, varFn, true, cloc);
			aggun = new AggregateUnaryOperator(agg, ReduceAll.getReduceAllFnObject(), numThreads);
		}
		else if ( opcode.equalsIgnoreCase("uarvar") ) {
			// RowVariances
			CM varFn = CM.getCMFnObject(AggregateOperationTypes.VARIANCE);
			CorrectionLocationType cloc = CorrectionLocationType.LASTFOURCOLUMNS;
			AggregateOperator agg = new AggregateOperator(0, varFn, true, cloc);
			aggun = new AggregateUnaryOperator(agg, ReduceCol.getReduceColFnObject(), numThreads);
		}
		else if ( opcode.equalsIgnoreCase("uacvar") ) {
			// ColVariances
			CM varFn = CM.getCMFnObject(AggregateOperationTypes.VARIANCE);
			CorrectionLocationType cloc = CorrectionLocationType.LASTFOURROWS;
			AggregateOperator agg = new AggregateOperator(0, varFn, true, cloc);
			aggun = new AggregateUnaryOperator(agg, ReduceRow.getReduceRowFnObject(), numThreads);
		}
		else if ( opcode.equalsIgnoreCase("ua+") ) {
			AggregateOperator agg = new AggregateOperator(0, Plus.getPlusFnObject());
			aggun = new AggregateUnaryOperator(agg, ReduceAll.getReduceAllFnObject(), numThreads);
		} 
		else if ( opcode.equalsIgnoreCase("uar+") ) {
			// RowSums
			AggregateOperator agg = new AggregateOperator(0, Plus.getPlusFnObject());
			aggun = new AggregateUnaryOperator(agg, ReduceCol.getReduceColFnObject(), numThreads);
		} 
		else if ( opcode.equalsIgnoreCase("uac+") ) {
			// ColSums
			AggregateOperator agg = new AggregateOperator(0, Plus.getPlusFnObject());
			aggun = new AggregateUnaryOperator(agg, ReduceRow.getReduceRowFnObject(), numThreads);
		}
		else if ( opcode.equalsIgnoreCase("ua*") ) {
			AggregateOperator agg = new AggregateOperator(1, Multiply.getMultiplyFnObject());
			aggun = new AggregateUnaryOperator(agg, ReduceAll.getReduceAllFnObject(), numThreads);
		} 
		else if ( opcode.equalsIgnoreCase("uar*") ) {
			AggregateOperator agg = new AggregateOperator(1, Multiply.getMultiplyFnObject());
			aggun = new AggregateUnaryOperator(agg, ReduceCol.getReduceColFnObject(), numThreads);
		} 
		else if ( opcode.equalsIgnoreCase("uac*") ) {
			AggregateOperator agg = new AggregateOperator(1, Multiply.getMultiplyFnObject());
			aggun = new AggregateUnaryOperator(agg, ReduceRow.getReduceRowFnObject(), numThreads);
		}
		else if ( opcode.equalsIgnoreCase("uamax") ) {
			AggregateOperator agg = new AggregateOperator(Double.NEGATIVE_INFINITY, Builtin.getBuiltinFnObject("max"));
			aggun = new AggregateUnaryOperator(agg, ReduceAll.getReduceAllFnObject(), numThreads);
		}
		else if ( opcode.equalsIgnoreCase("uamin") ) {
			AggregateOperator agg = new AggregateOperator(Double.POSITIVE_INFINITY, Builtin.getBuiltinFnObject("min"));
			aggun = new AggregateUnaryOperator(agg, ReduceAll.getReduceAllFnObject(), numThreads);
		} 
		else if ( opcode.equalsIgnoreCase("uatrace") ) {
			AggregateOperator agg = new AggregateOperator(0, Plus.getPlusFnObject());
			aggun = new AggregateUnaryOperator(agg, ReduceDiag.getReduceDiagFnObject(), numThreads);
		} 
		else if ( opcode.equalsIgnoreCase("uaktrace") ) {
			AggregateOperator agg = new AggregateOperator(0, KahanPlus.getKahanPlusFnObject(), true, CorrectionLocationType.LASTCOLUMN);
			aggun = new AggregateUnaryOperator(agg, ReduceDiag.getReduceDiagFnObject(), numThreads);
		} 		
		else if ( opcode.equalsIgnoreCase("uarmax") ) {
			AggregateOperator agg = new AggregateOperator(Double.NEGATIVE_INFINITY, Builtin.getBuiltinFnObject("max"));
			aggun = new AggregateUnaryOperator(agg, ReduceCol.getReduceColFnObject(), numThreads);
		} 
		else if (opcode.equalsIgnoreCase("uarimax") ) {
			AggregateOperator agg = new AggregateOperator(Double.NEGATIVE_INFINITY, Builtin.getBuiltinFnObject("maxindex"), true, CorrectionLocationType.LASTCOLUMN);
			aggun = new AggregateUnaryOperator(agg, ReduceCol.getReduceColFnObject(), numThreads);
		}
		else if ( opcode.equalsIgnoreCase("uarmin") ) {
			AggregateOperator agg = new AggregateOperator(Double.POSITIVE_INFINITY, Builtin.getBuiltinFnObject("min"));
			aggun = new AggregateUnaryOperator(agg, ReduceCol.getReduceColFnObject(), numThreads);
		} 
		else if (opcode.equalsIgnoreCase("uarimin") ) {
			AggregateOperator agg = new AggregateOperator(Double.POSITIVE_INFINITY, Builtin.getBuiltinFnObject("minindex"), true, CorrectionLocationType.LASTCOLUMN);
			aggun = new AggregateUnaryOperator(agg, ReduceCol.getReduceColFnObject(), numThreads);
		}
		else if ( opcode.equalsIgnoreCase("uacmax") ) {
			AggregateOperator agg = new AggregateOperator(Double.NEGATIVE_INFINITY, Builtin.getBuiltinFnObject("max"));
			aggun = new AggregateUnaryOperator(agg, ReduceRow.getReduceRowFnObject(), numThreads);
		} 
		else if ( opcode.equalsIgnoreCase("uacmin") ) {
			AggregateOperator agg = new AggregateOperator(Double.POSITIVE_INFINITY, Builtin.getBuiltinFnObject("min"));
			aggun = new AggregateUnaryOperator(agg, ReduceRow.getReduceRowFnObject(), numThreads);
		}
		
		return aggun;
	}

	public static AggregateTernaryOperator parseAggregateTernaryOperator(String opcode) {
		return parseAggregateTernaryOperator(opcode, 1);
	}
	
	public static AggregateTernaryOperator parseAggregateTernaryOperator(String opcode, int numThreads) {
		CorrectionLocationType corr = opcode.equalsIgnoreCase("tak+*") ? 
				CorrectionLocationType.LASTCOLUMN : CorrectionLocationType.LASTROW;
		AggregateOperator agg = new AggregateOperator(0, KahanPlus.getKahanPlusFnObject(), true, corr);
		IndexFunction ixfun = opcode.equalsIgnoreCase("tak+*") ? 
			ReduceAll.getReduceAllFnObject() : ReduceRow.getReduceRowFnObject();
		
		return new AggregateTernaryOperator(Multiply.getMultiplyFnObject(), agg, ixfun, numThreads);
	}
	
	public static AggregateOperator parseAggregateOperator(String opcode, String corrExists, String corrLoc)
	{
		AggregateOperator agg = null;
	
		if ( opcode.equalsIgnoreCase("ak+") || opcode.equalsIgnoreCase("aktrace") ) {
			boolean lcorrExists = (corrExists==null) ? true : Boolean.parseBoolean(corrExists);
			CorrectionLocationType lcorrLoc = (corrLoc==null) ? CorrectionLocationType.LASTCOLUMN : CorrectionLocationType.valueOf(corrLoc);
			agg = new AggregateOperator(0, KahanPlus.getKahanPlusFnObject(), lcorrExists, lcorrLoc);
		}
		else if ( opcode.equalsIgnoreCase("asqk+") ) {
			boolean lcorrExists = (corrExists==null) ? true : Boolean.parseBoolean(corrExists);
			CorrectionLocationType lcorrLoc = (corrLoc==null) ? CorrectionLocationType.LASTCOLUMN : CorrectionLocationType.valueOf(corrLoc);
			agg = new AggregateOperator(0, KahanPlusSq.getKahanPlusSqFnObject(), lcorrExists, lcorrLoc);
		}
		else if ( opcode.equalsIgnoreCase("a+") ) {
			agg = new AggregateOperator(0, Plus.getPlusFnObject());
		} 
		else if ( opcode.equalsIgnoreCase("a*") ) {
			agg = new AggregateOperator(1, Multiply.getMultiplyFnObject());
		}
		else if (opcode.equalsIgnoreCase("arimax")){
			agg = new AggregateOperator(Double.NEGATIVE_INFINITY, Builtin.getBuiltinFnObject("maxindex"), true, CorrectionLocationType.LASTCOLUMN);
		}
		else if ( opcode.equalsIgnoreCase("amax") ) {
			agg = new AggregateOperator(Double.NEGATIVE_INFINITY, Builtin.getBuiltinFnObject("max"));
		}
		else if ( opcode.equalsIgnoreCase("amin") ) {
			agg = new AggregateOperator(Double.POSITIVE_INFINITY, Builtin.getBuiltinFnObject("min"));
		}
		else if (opcode.equalsIgnoreCase("arimin")){
			agg = new AggregateOperator(Double.POSITIVE_INFINITY, Builtin.getBuiltinFnObject("minindex"), true, CorrectionLocationType.LASTCOLUMN);
		}
		else if ( opcode.equalsIgnoreCase("amean") ) {
			boolean lcorrExists = (corrExists==null) ? true : Boolean.parseBoolean(corrExists);
			CorrectionLocationType lcorrLoc = (corrLoc==null) ? CorrectionLocationType.LASTTWOCOLUMNS : CorrectionLocationType.valueOf(corrLoc);
			agg = new AggregateOperator(0, KahanPlus.getKahanPlusFnObject(), lcorrExists, lcorrLoc);
		}
		else if ( opcode.equalsIgnoreCase("avar") ) {
			boolean lcorrExists = (corrExists==null) ? true : Boolean.parseBoolean(corrExists);
			CorrectionLocationType lcorrLoc = (corrLoc==null) ?
					CorrectionLocationType.LASTFOURCOLUMNS :
					CorrectionLocationType.valueOf(corrLoc);
			CM varFn = CM.getCMFnObject(AggregateOperationTypes.VARIANCE);
			agg = new AggregateOperator(0, varFn, lcorrExists, lcorrLoc);
		}

		return agg;
	}

	public static AggregateUnaryOperator parseBasicCumulativeAggregateUnaryOperator(UnaryOperator uop)
	{
		Builtin f = (Builtin)uop.fn;
		
		if( f.getBuiltinCode()==BuiltinCode.CUMSUM ) 
			return parseBasicAggregateUnaryOperator("uack+") ;
		else if( f.getBuiltinCode()==BuiltinCode.CUMPROD ) 
			return parseBasicAggregateUnaryOperator("uac*") ;
		else if( f.getBuiltinCode()==BuiltinCode.CUMMIN ) 
			return parseBasicAggregateUnaryOperator("uacmin") ;
		else if( f.getBuiltinCode()==BuiltinCode.CUMMAX ) 
			return parseBasicAggregateUnaryOperator("uacmax" ) ;
		
		throw new RuntimeException("Unsupported cumulative aggregate unary operator: "+f.getBuiltinCode());
	}

	public static AggregateUnaryOperator parseCumulativeAggregateUnaryOperator(String opcode)
	{
		AggregateUnaryOperator aggun = null;
		if( "ucumack+".equals(opcode) ) { 
			AggregateOperator agg = new AggregateOperator(0, KahanPlus.getKahanPlusFnObject(), true, CorrectionLocationType.LASTROW);
			aggun = new AggregateUnaryOperator(agg, ReduceRow.getReduceRowFnObject());
		}
		else if ( "ucumac*".equals(opcode) ) { 
			AggregateOperator agg = new AggregateOperator(0, Multiply.getMultiplyFnObject(), false, CorrectionLocationType.NONE);
			aggun = new AggregateUnaryOperator(agg, ReduceRow.getReduceRowFnObject());
		}
		else if ( "ucumacmin".equals(opcode) ) { 
			AggregateOperator agg = new AggregateOperator(0, Builtin.getBuiltinFnObject("min"), false, CorrectionLocationType.NONE);
			aggun = new AggregateUnaryOperator(agg, ReduceRow.getReduceRowFnObject());
		}
		else if ( "ucumacmax".equals(opcode) ) { 
			AggregateOperator agg = new AggregateOperator(0, Builtin.getBuiltinFnObject("max"), false, CorrectionLocationType.NONE);
			aggun = new AggregateUnaryOperator(agg, ReduceRow.getReduceRowFnObject());
		}
		
		return aggun;
	}
	
	public static UnaryOperator parseUnaryOperator(String opcode) {
		return opcode.equals("!") ?
			new UnaryOperator(Not.getNotFnObject()) :
			new UnaryOperator(Builtin.getBuiltinFnObject(opcode));
	}

	public static Operator parseBinaryOrBuiltinOperator(String opcode, CPOperand in1, CPOperand in2) {
		if( LibCommonsMath.isSupportedMatrixMatrixOperation(opcode) )
			return null;
		boolean matrixScalar = (in1.getDataType() != in2.getDataType());
		return Builtin.isBuiltinFnObject(opcode) ?
			(matrixScalar ? new RightScalarOperator( Builtin.getBuiltinFnObject(opcode), 0) :
				new BinaryOperator( Builtin.getBuiltinFnObject(opcode))) :
			(matrixScalar ? parseScalarBinaryOperator(opcode, in1.getDataType().isScalar()) :
				parseBinaryOperator(opcode));
	}
	
	public static Operator parseExtendedBinaryOrBuiltinOperator(String opcode, CPOperand in1, CPOperand in2) {
		boolean matrixScalar = (in1.getDataType() != in2.getDataType());
		return Builtin.isBuiltinFnObject(opcode) ?
			(matrixScalar ? new RightScalarOperator( Builtin.getBuiltinFnObject(opcode), 0) :
				new BinaryOperator( Builtin.getBuiltinFnObject(opcode))) :
			(matrixScalar ? parseScalarBinaryOperator(opcode, in1.getDataType().isScalar()) :
				parseExtendedBinaryOperator(opcode));
	}
	
	public static BinaryOperator parseBinaryOperator(String opcode) 
	{
		if(opcode.equalsIgnoreCase("=="))
			return new BinaryOperator(Equals.getEqualsFnObject());
		else if(opcode.equalsIgnoreCase("!="))
			return new BinaryOperator(NotEquals.getNotEqualsFnObject());
		else if(opcode.equalsIgnoreCase("<"))
			return new BinaryOperator(LessThan.getLessThanFnObject());
		else if(opcode.equalsIgnoreCase(">"))
			return new BinaryOperator(GreaterThan.getGreaterThanFnObject());
		else if(opcode.equalsIgnoreCase("<="))
			return new BinaryOperator(LessThanEquals.getLessThanEqualsFnObject());
		else if(opcode.equalsIgnoreCase(">="))
			return new BinaryOperator(GreaterThanEquals.getGreaterThanEqualsFnObject());
		else if(opcode.equalsIgnoreCase("&&"))
			return new BinaryOperator(And.getAndFnObject());
		else if(opcode.equalsIgnoreCase("||"))
			return new BinaryOperator(Or.getOrFnObject());
		else if(opcode.equalsIgnoreCase("xor"))
			return new BinaryOperator(Xor.getXorFnObject());
		else if(opcode.equalsIgnoreCase("bitwAnd"))
			return new BinaryOperator(BitwAnd.getBitwAndFnObject());
		else if(opcode.equalsIgnoreCase("bitwOr"))
			return new BinaryOperator(BitwOr.getBitwOrFnObject());
		else if(opcode.equalsIgnoreCase("bitwXor"))
			return new BinaryOperator(BitwXor.getBitwXorFnObject());
		else if(opcode.equalsIgnoreCase("bitwShiftL"))
			return new BinaryOperator(BitwShiftL.getBitwShiftLFnObject());
		else if(opcode.equalsIgnoreCase("bitwShiftR"))
			return new BinaryOperator(BitwShiftR.getBitwShiftRFnObject());
		else if(opcode.equalsIgnoreCase("+"))
			return new BinaryOperator(Plus.getPlusFnObject());
		else if(opcode.equalsIgnoreCase("-"))
			return new BinaryOperator(Minus.getMinusFnObject());
		else if(opcode.equalsIgnoreCase("*"))
			return new BinaryOperator(Multiply.getMultiplyFnObject());
		else if(opcode.equalsIgnoreCase("1-*"))
			return new BinaryOperator(Minus1Multiply.getMinus1MultiplyFnObject());
		else if ( opcode.equalsIgnoreCase("*2") ) 
			return new BinaryOperator(Multiply2.getMultiply2FnObject());
		else if(opcode.equalsIgnoreCase("/"))
			return new BinaryOperator(Divide.getDivideFnObject());
		else if(opcode.equalsIgnoreCase("%%"))
			return new BinaryOperator(Modulus.getFnObject());
		else if(opcode.equalsIgnoreCase("%/%"))
			return new BinaryOperator(IntegerDivide.getFnObject());
		else if(opcode.equalsIgnoreCase("^"))
			return new BinaryOperator(Power.getPowerFnObject());
		else if ( opcode.equalsIgnoreCase("^2") )
			return new BinaryOperator(Power2.getPower2FnObject());
		else if ( opcode.equalsIgnoreCase("max") ) 
			return new BinaryOperator(Builtin.getBuiltinFnObject("max"));
		else if ( opcode.equalsIgnoreCase("min") ) 
			return new BinaryOperator(Builtin.getBuiltinFnObject("min"));
		
		throw new RuntimeException("Unknown binary opcode " + opcode);
	}
	
	public static TernaryOperator parseTernaryOperator(String opcode) {
		return new TernaryOperator(opcode.equals("+*") ? PlusMultiply.getFnObject() :
			opcode.equals("-*") ? MinusMultiply.getFnObject() : IfElse.getFnObject());
	}
	
	/**
	 * scalar-matrix operator
	 * 
	 * @param opcode the opcode
	 * @param arg1IsScalar ?
	 * @return scalar operator
	 */
	public static ScalarOperator parseScalarBinaryOperator(String opcode, boolean arg1IsScalar) 
	{
		//for all runtimes that set constant dynamically (cp/spark)
		double default_constant = 0;
		
		return parseScalarBinaryOperator(opcode, arg1IsScalar, default_constant);
	}
	
	/**
	 * scalar-matrix operator
	 * 
	 * @param opcode the opcode
	 * @param arg1IsScalar ?
	 * @param constant ?
	 * @return scalar operator
	 */
	public static ScalarOperator parseScalarBinaryOperator(String opcode, boolean arg1IsScalar, double constant)
	{
		//commutative operators
		if ( opcode.equalsIgnoreCase("+") ){ 
			return new RightScalarOperator(Plus.getPlusFnObject(), constant); 
		}
		else if ( opcode.equalsIgnoreCase("*") ) {
			return new RightScalarOperator(Multiply.getMultiplyFnObject(), constant);
		} 
		//non-commutative operators
		else if ( opcode.equalsIgnoreCase("-") ) {
			if(arg1IsScalar)
				return new LeftScalarOperator(Minus.getMinusFnObject(), constant);
			else return new RightScalarOperator(Minus.getMinusFnObject(), constant);
		}
		else if ( opcode.equalsIgnoreCase("-nz") ) {
			//no support for left scalar yet
			return new RightScalarOperator(MinusNz.getMinusNzFnObject(), constant);
		}
		else if ( opcode.equalsIgnoreCase("/") ) {
			if(arg1IsScalar)
				return new LeftScalarOperator(Divide.getDivideFnObject(), constant);
			else return new RightScalarOperator(Divide.getDivideFnObject(), constant);
		}  
		else if ( opcode.equalsIgnoreCase("%%") ) {
			if(arg1IsScalar)
				return new LeftScalarOperator(Modulus.getFnObject(), constant);
			else return new RightScalarOperator(Modulus.getFnObject(), constant);
		}
		else if ( opcode.equalsIgnoreCase("%/%") ) {
			if(arg1IsScalar)
				return new LeftScalarOperator(IntegerDivide.getFnObject(), constant);
			else return new RightScalarOperator(IntegerDivide.getFnObject(), constant);
		}
		else if ( opcode.equalsIgnoreCase("^") ){
			if(arg1IsScalar)
				return new LeftScalarOperator(Power.getPowerFnObject(), constant);
			else return new RightScalarOperator(Power.getPowerFnObject(), constant);
		}
		else if ( opcode.equalsIgnoreCase("max") ) {
			return new RightScalarOperator(Builtin.getBuiltinFnObject("max"), constant);
		}
		else if ( opcode.equalsIgnoreCase("min") ) {
			return new RightScalarOperator(Builtin.getBuiltinFnObject("min"), constant);
		}
		else if ( opcode.equalsIgnoreCase("log") || opcode.equalsIgnoreCase("log_nz") ){
			if( arg1IsScalar )
				return new LeftScalarOperator(Builtin.getBuiltinFnObject(opcode), constant);
			return new RightScalarOperator(Builtin.getBuiltinFnObject(opcode), constant);
		}
		else if ( opcode.equalsIgnoreCase(">") ) {
			if(arg1IsScalar)
				return new LeftScalarOperator(GreaterThan.getGreaterThanFnObject(), constant);
			return new RightScalarOperator(GreaterThan.getGreaterThanFnObject(), constant);
		}
		else if ( opcode.equalsIgnoreCase(">=") ) {
			if(arg1IsScalar)
				return new LeftScalarOperator(GreaterThanEquals.getGreaterThanEqualsFnObject(), constant);
			return new RightScalarOperator(GreaterThanEquals.getGreaterThanEqualsFnObject(), constant);
		}
		else if ( opcode.equalsIgnoreCase("<") ) {
			if(arg1IsScalar)
				return new LeftScalarOperator(LessThan.getLessThanFnObject(), constant);
			return new RightScalarOperator(LessThan.getLessThanFnObject(), constant);
		}
		else if ( opcode.equalsIgnoreCase("<=") ) {
			if(arg1IsScalar)
				return new LeftScalarOperator(LessThanEquals.getLessThanEqualsFnObject(), constant);
			return new RightScalarOperator(LessThanEquals.getLessThanEqualsFnObject(), constant);
		}
		else if ( opcode.equalsIgnoreCase("==") ) {
			if(arg1IsScalar)
				return new LeftScalarOperator(Equals.getEqualsFnObject(), constant);
			return new RightScalarOperator(Equals.getEqualsFnObject(), constant);
		}
		else if ( opcode.equalsIgnoreCase("!=") ) {
			if(arg1IsScalar)
				return new LeftScalarOperator(NotEquals.getNotEqualsFnObject(), constant);
			return new RightScalarOperator(NotEquals.getNotEqualsFnObject(), constant);
		}
		else if ( opcode.equalsIgnoreCase("&&") ) {
			return arg1IsScalar ?
				new LeftScalarOperator(And.getAndFnObject(), constant) :
				new RightScalarOperator(And.getAndFnObject(), constant);
		}
		else if ( opcode.equalsIgnoreCase("||") ) {
			return arg1IsScalar ?
				new LeftScalarOperator(Or.getOrFnObject(), constant) :
				new RightScalarOperator(Or.getOrFnObject(), constant);
		}
		else if ( opcode.equalsIgnoreCase("xor") ) {
			return arg1IsScalar ?
				new LeftScalarOperator(Xor.getXorFnObject(), constant) :
				new RightScalarOperator(Xor.getXorFnObject(), constant);
		}
		else if ( opcode.equalsIgnoreCase("bitwAnd") ) {
			return arg1IsScalar ?
				new LeftScalarOperator(BitwAnd.getBitwAndFnObject(), constant) :
				new RightScalarOperator(BitwAnd.getBitwAndFnObject(), constant);
		}
		else if ( opcode.equalsIgnoreCase("bitwOr") ) {
			return arg1IsScalar ?
				new LeftScalarOperator(BitwOr.getBitwOrFnObject(), constant) :
				new RightScalarOperator(BitwOr.getBitwOrFnObject(), constant);
		}
		else if ( opcode.equalsIgnoreCase("bitwXor") ) {
			return arg1IsScalar ?
				new LeftScalarOperator(BitwXor.getBitwXorFnObject(), constant) :
				new RightScalarOperator(BitwXor.getBitwXorFnObject(), constant);
		}
		else if ( opcode.equalsIgnoreCase("bitwShiftL") ) {
			return arg1IsScalar ?
				new LeftScalarOperator(BitwShiftL.getBitwShiftLFnObject(), constant) :
				new RightScalarOperator(BitwShiftL.getBitwShiftLFnObject(), constant);
		}
		else if ( opcode.equalsIgnoreCase("bitwShiftR") ) {
			return arg1IsScalar ?
				new LeftScalarOperator(BitwShiftR.getBitwShiftRFnObject(), constant) :
				new RightScalarOperator(BitwShiftR.getBitwShiftRFnObject(), constant);
		}
		//operations that only exist for performance purposes (all unary or commutative operators)
		else if ( opcode.equalsIgnoreCase("*2") ) {
			return new RightScalarOperator(Multiply2.getMultiply2FnObject(), constant);
		} 
		else if ( opcode.equalsIgnoreCase("^2") ){
			return new RightScalarOperator(Power2.getPower2FnObject(), constant);
		}
		else if ( opcode.equalsIgnoreCase("1-*") ) {
			return new RightScalarOperator(Minus1Multiply.getMinus1MultiplyFnObject(), constant);
		}
		
		//operations that only exist in mr
		else if ( opcode.equalsIgnoreCase("s-r") ) {
			return new LeftScalarOperator(Minus.getMinusFnObject(), constant);
		} 
		else if ( opcode.equalsIgnoreCase("so") ) {
			return new LeftScalarOperator(Divide.getDivideFnObject(), constant);
		}
		
		throw new RuntimeException("Unknown binary opcode " + opcode);
	}

	public static BinaryOperator parseExtendedBinaryOperator(String opcode) {
		if(opcode.equalsIgnoreCase("==") || opcode.equalsIgnoreCase("map=="))
			return new BinaryOperator(Equals.getEqualsFnObject());
		else if(opcode.equalsIgnoreCase("!=") || opcode.equalsIgnoreCase("map!="))
			return new BinaryOperator(NotEquals.getNotEqualsFnObject());
		else if(opcode.equalsIgnoreCase("<") || opcode.equalsIgnoreCase("map<"))
			return new BinaryOperator(LessThan.getLessThanFnObject());
		else if(opcode.equalsIgnoreCase(">") || opcode.equalsIgnoreCase("map>"))
			return new BinaryOperator(GreaterThan.getGreaterThanFnObject());
		else if(opcode.equalsIgnoreCase("<=") || opcode.equalsIgnoreCase("map<="))
			return new BinaryOperator(LessThanEquals.getLessThanEqualsFnObject());
		else if(opcode.equalsIgnoreCase(">=") || opcode.equalsIgnoreCase("map>="))
			return new BinaryOperator(GreaterThanEquals.getGreaterThanEqualsFnObject());
		else if(opcode.equalsIgnoreCase("&&") || opcode.equalsIgnoreCase("map&&"))
			return new BinaryOperator(And.getAndFnObject());
		else if(opcode.equalsIgnoreCase("||") || opcode.equalsIgnoreCase("map||"))
			return new BinaryOperator(Or.getOrFnObject());
		else if(opcode.equalsIgnoreCase("xor") || opcode.equalsIgnoreCase("mapxor"))
			return new BinaryOperator(Xor.getXorFnObject());
		else if(opcode.equalsIgnoreCase("bitwAnd") || opcode.equalsIgnoreCase("mapbitwAnd"))
			return new BinaryOperator(BitwAnd.getBitwAndFnObject());
		else if(opcode.equalsIgnoreCase("bitwOr") || opcode.equalsIgnoreCase("mapbitwOr"))
			return new BinaryOperator(BitwOr.getBitwOrFnObject());
		else if(opcode.equalsIgnoreCase("bitwXor") || opcode.equalsIgnoreCase("mapbitwXor"))
			return new BinaryOperator(BitwXor.getBitwXorFnObject());
		else if(opcode.equalsIgnoreCase("bitwShiftL") || opcode.equalsIgnoreCase("mapbitwShiftL"))
			return new BinaryOperator(BitwShiftL.getBitwShiftLFnObject());
		else if(opcode.equalsIgnoreCase("bitwShiftR") || opcode.equalsIgnoreCase("mapbitwShiftR"))
			return new BinaryOperator(BitwShiftR.getBitwShiftRFnObject());
		else if(opcode.equalsIgnoreCase("+") || opcode.equalsIgnoreCase("map+"))
			return new BinaryOperator(Plus.getPlusFnObject());
		else if(opcode.equalsIgnoreCase("-") || opcode.equalsIgnoreCase("map-"))
			return new BinaryOperator(Minus.getMinusFnObject());
		else if(opcode.equalsIgnoreCase("*") || opcode.equalsIgnoreCase("map*"))
			return new BinaryOperator(Multiply.getMultiplyFnObject());
		else if(opcode.equalsIgnoreCase("1-*") || opcode.equalsIgnoreCase("map1-*"))
			return new BinaryOperator(Minus1Multiply.getMinus1MultiplyFnObject());
		else if ( opcode.equalsIgnoreCase("*2") ) 
			return new BinaryOperator(Multiply2.getMultiply2FnObject());
		else if(opcode.equalsIgnoreCase("/") || opcode.equalsIgnoreCase("map/"))
			return new BinaryOperator(Divide.getDivideFnObject());
		else if(opcode.equalsIgnoreCase("%%") || opcode.equalsIgnoreCase("map%%"))
			return new BinaryOperator(Modulus.getFnObject());
		else if(opcode.equalsIgnoreCase("%/%") || opcode.equalsIgnoreCase("map%/%"))
			return new BinaryOperator(IntegerDivide.getFnObject());
		else if(opcode.equalsIgnoreCase("^") || opcode.equalsIgnoreCase("map^"))
			return new BinaryOperator(Power.getPowerFnObject());
		else if ( opcode.equalsIgnoreCase("^2") )
			return new BinaryOperator(Power2.getPower2FnObject());
		else if ( opcode.equalsIgnoreCase("max") || opcode.equalsIgnoreCase("mapmax") ) 
			return new BinaryOperator(Builtin.getBuiltinFnObject("max"));
		else if ( opcode.equalsIgnoreCase("min") || opcode.equalsIgnoreCase("mapmin") ) 
			return new BinaryOperator(Builtin.getBuiltinFnObject("min"));
		
		throw new DMLRuntimeException("Unknown binary opcode " + opcode);
	}

	public static String deriveAggregateOperatorOpcode(String opcode)
	{
		if ( opcode.equalsIgnoreCase("uak+") || opcode.equalsIgnoreCase("uark+") || opcode.equalsIgnoreCase("uack+"))
			return "ak+";
		else if ( opcode.equalsIgnoreCase("uasqk+") || opcode.equalsIgnoreCase("uarsqk+") || opcode.equalsIgnoreCase("uacsqk+") )
			return "asqk+";
		else if ( opcode.equalsIgnoreCase("uamean") || opcode.equalsIgnoreCase("uarmean") || opcode.equalsIgnoreCase("uacmean") )
			return "amean";
		else if ( opcode.equalsIgnoreCase("uavar") || opcode.equalsIgnoreCase("uarvar") || opcode.equalsIgnoreCase("uacvar") )
			return "avar";
		else if ( opcode.equalsIgnoreCase("ua+") || opcode.equalsIgnoreCase("uar+") || opcode.equalsIgnoreCase("uac+") )
			return "a+";
		else if ( opcode.equalsIgnoreCase("ua*") || opcode.equalsIgnoreCase("uar*") || opcode.equalsIgnoreCase("uac*") )
			return "a*";
		else if ( opcode.equalsIgnoreCase("uatrace") || opcode.equalsIgnoreCase("uaktrace") ) 
			return "aktrace";
		else if ( opcode.equalsIgnoreCase("uamax") || opcode.equalsIgnoreCase("uarmax") || opcode.equalsIgnoreCase("uacmax") )
			return "amax";
		else if ( opcode.equalsIgnoreCase("uamin") || opcode.equalsIgnoreCase("uarmin") || opcode.equalsIgnoreCase("uacmin") )
			return "amin";
		else if (opcode.equalsIgnoreCase("uarimax") )
			return "arimax";
		else if (opcode.equalsIgnoreCase("uarimin") )
			return "arimin";
	
		return null;
	}

	public static CorrectionLocationType deriveAggregateOperatorCorrectionLocation(String opcode)
	{
		if ( opcode.equalsIgnoreCase("uak+") || opcode.equalsIgnoreCase("uark+") ||
				opcode.equalsIgnoreCase("uasqk+") || opcode.equalsIgnoreCase("uarsqk+") ||
				opcode.equalsIgnoreCase("uatrace") || opcode.equalsIgnoreCase("uaktrace") )
			return CorrectionLocationType.LASTCOLUMN;
		else if ( opcode.equalsIgnoreCase("uack+") || opcode.equalsIgnoreCase("uacsqk+") )
			return CorrectionLocationType.LASTROW;
		else if ( opcode.equalsIgnoreCase("uamean") || opcode.equalsIgnoreCase("uarmean") )
			return CorrectionLocationType.LASTTWOCOLUMNS;
		else if ( opcode.equalsIgnoreCase("uacmean") )
			return CorrectionLocationType.LASTTWOROWS;
		else if ( opcode.equalsIgnoreCase("uavar") || opcode.equalsIgnoreCase("uarvar") )
			return CorrectionLocationType.LASTFOURCOLUMNS;
		else if ( opcode.equalsIgnoreCase("uacvar") )
			return CorrectionLocationType.LASTFOURROWS;
		else if (opcode.equalsIgnoreCase("uarimax") || opcode.equalsIgnoreCase("uarimin") )
			return CorrectionLocationType.LASTCOLUMN;
		
		return CorrectionLocationType.NONE;
	}

	public static boolean isDistQuaternaryOpcode(String opcode) 
	{
		return WeightedSquaredLoss.OPCODE.equalsIgnoreCase(opcode)     //mapwsloss
			|| WeightedSquaredLossR.OPCODE.equalsIgnoreCase(opcode)    //redwsloss
			|| WeightedSigmoid.OPCODE.equalsIgnoreCase(opcode)   	   //mapwsigmoid
			|| WeightedSigmoidR.OPCODE.equalsIgnoreCase(opcode)        //redwsigmoid
			|| WeightedDivMM.OPCODE.equalsIgnoreCase(opcode)           //mapwdivmm
			|| WeightedDivMMR.OPCODE.equalsIgnoreCase(opcode)          //redwdivmm
			|| WeightedCrossEntropy.OPCODE.equalsIgnoreCase(opcode)    //mapwcemm
			|| WeightedCrossEntropyR.OPCODE.equalsIgnoreCase(opcode)   //redwcemm
			|| WeightedUnaryMM.OPCODE.equalsIgnoreCase(opcode)         //mapwumm
			|| WeightedUnaryMMR.OPCODE.equalsIgnoreCase(opcode);       //redwumm
	}
	
	public static AggregateBinaryOperator getMatMultOperator(int k) {
		AggregateOperator agg = new AggregateOperator(0, Plus.getPlusFnObject());
		return new AggregateBinaryOperator(Multiply.getMultiplyFnObject(), agg, k);
	}
}

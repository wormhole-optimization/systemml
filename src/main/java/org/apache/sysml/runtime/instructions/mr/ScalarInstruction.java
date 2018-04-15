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

package org.apache.sysml.runtime.instructions.mr;

import java.util.ArrayList;

import org.apache.sysml.lops.Lop;
import org.apache.sysml.parser.Expression.DataType;
import org.apache.sysml.runtime.instructions.InstructionUtils;
import org.apache.sysml.runtime.matrix.data.MatrixValue;
import org.apache.sysml.runtime.matrix.mapred.CachedValueMap;
import org.apache.sysml.runtime.matrix.mapred.IndexedMatrixValue;
import org.apache.sysml.runtime.matrix.operators.ScalarOperator;

public class ScalarInstruction extends UnaryMRInstructionBase {

	private ScalarInstruction(ScalarOperator op, byte in, byte out, String istr) {
		super(MRType.Binary, op, in, out);
		instString = istr;
	}

	public static ScalarInstruction parseInstruction ( String str ) {
		InstructionUtils.checkNumFields ( str, 3 );
		String[] parts = InstructionUtils.getInstructionParts ( str );
		String opcode = parts[0];
		boolean firstArgScalar = isFirstArgumentScalar(str);
		double cst = Double.parseDouble( firstArgScalar ? parts[1] : parts[2]);
		byte in = Byte.parseByte( firstArgScalar ? parts[2] : parts[1]);
		byte out = Byte.parseByte(parts[3]);
		ScalarOperator sop = InstructionUtils.parseScalarBinaryOperator(opcode, firstArgScalar, cst);
		return new ScalarInstruction(sop, in, out, str);
	}
	
	@Override
	public void processInstruction(Class<? extends MatrixValue> valueClass, CachedValueMap cachedValues, 
			IndexedMatrixValue tempValue, IndexedMatrixValue zeroInput, int blockRowFactor, int blockColFactor)
	{
		ArrayList<IndexedMatrixValue> blkList = cachedValues.get(input);
		if( blkList != null )
			for( IndexedMatrixValue in : blkList ) {
				if(in==null) continue;
			
				//allocate space for the output value
				IndexedMatrixValue out = (input==output) ? tempValue :
					cachedValues.holdPlace(output, valueClass);
				
				//process instruction
				out.getIndexes().setIndexes(in.getIndexes());
				in.getValue().scalarOperations((ScalarOperator)this.optr, out.getValue());
				
				//put the output value in the cache
				if(out==tempValue)
					cachedValues.add(output, out);
			}
	}

	private static boolean isFirstArgumentScalar(String inst) {
		//get first argument
		String[] parts = InstructionUtils.getInstructionPartsWithValueType(inst);
		String arg1 = parts[1];
		
		//get data type of first argument
		String[] subparts = arg1.split(Lop.VALUETYPE_PREFIX);
		DataType dt = DataType.valueOf(subparts[1]);
		
		return (dt == DataType.SCALAR);
	}
}

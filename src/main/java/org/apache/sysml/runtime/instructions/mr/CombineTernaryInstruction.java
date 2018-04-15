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

import org.apache.sysml.lops.Ctable.OperationTypes;
import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.instructions.InstructionUtils;
import org.apache.sysml.runtime.matrix.data.MatrixValue;
import org.apache.sysml.runtime.matrix.mapred.CachedValueMap;
import org.apache.sysml.runtime.matrix.mapred.IndexedMatrixValue;

public class CombineTernaryInstruction extends CtableInstruction {

	private CombineTernaryInstruction(OperationTypes op, byte in1, byte in2, byte in3, byte out, String istr) {
		super(MRType.CombineTernary, op, in1, in2, in3, out, -1, -1, istr);
	}

	public static CombineTernaryInstruction parseInstruction ( String str ) {
		// example instruction string - ctabletransform:::0:DOUBLE:::1:DOUBLE:::2:DOUBLE:::3:DOUBLE 
		InstructionUtils.checkNumFields ( str, 4 );
		String[] parts = InstructionUtils.getInstructionParts ( str );
		byte in1, in2, in3, out;
		String opcode = parts[0];
		in1 = Byte.parseByte(parts[1]);
		in2 = Byte.parseByte(parts[2]);
		in3 = Byte.parseByte(parts[3]);
		out = Byte.parseByte(parts[4]);
		if ( opcode.equalsIgnoreCase("combineternary") )
			return new CombineTernaryInstruction(null, in1, in2, in3, out, str);
		return null;
	}
	
	@Override
	public void processInstruction(Class<? extends MatrixValue> valueClass,
			CachedValueMap cachedValues, IndexedMatrixValue tempValue, IndexedMatrixValue zeroInput, 
			int blockRowFactor, int blockColFactor) {
		throw new DMLRuntimeException("CombineTernaryInstruction.processInstruction should never be called!");
	}
}

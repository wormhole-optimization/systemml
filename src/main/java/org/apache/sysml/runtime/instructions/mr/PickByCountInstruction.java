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

import org.apache.sysml.lops.PickByCount.OperationTypes;
import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.instructions.InstructionUtils;
import org.apache.sysml.runtime.matrix.data.MatrixValue;
import org.apache.sysml.runtime.matrix.mapred.CachedValueMap;
import org.apache.sysml.runtime.matrix.mapred.IndexedMatrixValue;
import org.apache.sysml.runtime.matrix.operators.Operator;

public class PickByCountInstruction extends MRInstruction {

	public byte input1; // used for both valuepick and rangepick
	public byte input2; // used only for valuepick
	public double cst; // used only for rangepick
	public boolean isValuePick = true;

	private PickByCountInstruction(Operator op, byte _in1, byte _in2, byte out, String istr) {
		super(MRType.PickByCount, op, out);
		input1 = _in1;
		input2 = _in2;
		cst = 0;
		instString = istr;
		isValuePick = true;
	}

	private PickByCountInstruction(Operator op, byte _in1, double _cst, byte out, String istr) {
		super(MRType.PickByCount, op, out);
		input1 = _in1;
		cst = _cst;
		instString = istr;
		isValuePick = false;
	}

	public static PickByCountInstruction parseInstruction ( String str ) {
		InstructionUtils.checkNumFields ( str, 5 );
		String[] parts = InstructionUtils.getInstructionParts ( str );
		OperationTypes ptype = OperationTypes.valueOf(parts[4]);
		if ( ptype == OperationTypes.VALUEPICK ) {
			byte in1 = Byte.parseByte(parts[1]);
			byte in2 = Byte.parseByte(parts[2]);
			byte out = Byte.parseByte(parts[3]);
			return new PickByCountInstruction(null, in1, in2, out, str);
		} 
		else if ( ptype == OperationTypes.RANGEPICK ) {
			byte in1 = Byte.parseByte(parts[1]);
			double cstant = Double.parseDouble(parts[2]);
			byte out = Byte.parseByte(parts[3]);
			return new PickByCountInstruction(null, in1, cstant, out, str);
		}
		return null;
	}

	@Override
	public void processInstruction(Class<? extends MatrixValue> valueClass,
			CachedValueMap cachedValues, IndexedMatrixValue tempValue,
			IndexedMatrixValue zeroInput, int blockRowFactor, int blockColFactor) {
		throw new DMLRuntimeException("PickByCountInstruction.processInstruction should never be called!");
	}

	@Override
	public byte[] getAllIndexes() {
		if( isValuePick ) {
			return new byte[]{input1,input2,output};
		}
		else { //range pick
			return new byte[]{input1, output};
		}
		
	}

	@Override
	public byte[] getInputIndexes() {
		if( isValuePick ) {
			return new byte[]{input1,input2};
		}
		else { //range pick
			return new byte[]{input1};
		}
	}
}

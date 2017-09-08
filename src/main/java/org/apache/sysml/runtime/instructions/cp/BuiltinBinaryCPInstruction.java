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

import org.apache.sysml.parser.Expression.DataType;
import org.apache.sysml.parser.Expression.ValueType;
import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.functionobjects.Builtin;
import org.apache.sysml.runtime.functionobjects.ValueFunction;
import org.apache.sysml.runtime.matrix.operators.BinaryOperator;
import org.apache.sysml.runtime.matrix.operators.Operator;
import org.apache.sysml.runtime.matrix.operators.RightScalarOperator;

public abstract class BuiltinBinaryCPInstruction extends BinaryCPInstruction {
	private int _arity;

	protected BuiltinBinaryCPInstruction(Operator op, CPOperand in1, CPOperand in2, CPOperand out, int arity,
			String opcode, String istr) {
		super(op, in1, in2, out, opcode, istr);
		_cptype = CPINSTRUCTION_TYPE.BuiltinBinary;
		_arity = arity;
	}

	public int getArity() {
		return _arity;
	}
	
	public static BuiltinBinaryCPInstruction parseInstruction ( String str ) 
		throws DMLRuntimeException {
		CPOperand in1 = new CPOperand("", ValueType.UNKNOWN, DataType.UNKNOWN);
		CPOperand in2 = new CPOperand("", ValueType.UNKNOWN, DataType.UNKNOWN);
		CPOperand out = new CPOperand("", ValueType.UNKNOWN, DataType.UNKNOWN);
		String opcode = parseBinaryInstruction(str, in1, in2, out);

		checkOutputDataType(in1, in2, out);
		
		// Determine appropriate Function Object based on opcode
		ValueFunction func = Builtin.getBuiltinFnObject(opcode);
			
		if ( in1.getDataType() == DataType.SCALAR && in2.getDataType() == DataType.SCALAR )
			return new ScalarScalarBuiltinCPInstruction(new BinaryOperator(func), in1, in2, out, opcode, str);
		else if ( in1.getDataType() == DataType.MATRIX && in2.getDataType() == DataType.MATRIX )
			return new MatrixMatrixBuiltinCPInstruction(new BinaryOperator(func), in1, in2, out, opcode, str);	
		else 
			return new MatrixScalarBuiltinCPInstruction(new RightScalarOperator(func, 0), in1, in2, out, opcode, str);
	}
}

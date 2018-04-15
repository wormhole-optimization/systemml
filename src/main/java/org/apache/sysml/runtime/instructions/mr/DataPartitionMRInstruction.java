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

import org.apache.sysml.runtime.instructions.InstructionUtils;
import org.apache.sysml.runtime.matrix.operators.Operator;

/**
 * Dummy instruction for cost estimation of data partition mr.
 * 
 */
public class DataPartitionMRInstruction extends UnaryInstruction {

	private DataPartitionMRInstruction(Operator op, byte in, byte out, String istr) {
		super(MRType.Partition, op, in, out, istr);
	}

	public static DataPartitionMRInstruction parseInstruction ( String str ) {
		InstructionUtils.checkNumFields ( str, 3 );
		String[] parts = InstructionUtils.getInstructionParts ( str );
		byte in, out;
		in = Byte.parseByte(parts[1]);
		out = Byte.parseByte(parts[2]);
		return new DataPartitionMRInstruction(null, in, out, str);
	}
}

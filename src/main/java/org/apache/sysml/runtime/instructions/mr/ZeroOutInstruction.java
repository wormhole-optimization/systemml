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

import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.instructions.InstructionUtils;
import org.apache.sysml.runtime.matrix.data.MatrixValue;
import org.apache.sysml.runtime.matrix.data.OperationsOnMatrixValues;
import org.apache.sysml.runtime.matrix.mapred.CachedValueMap;
import org.apache.sysml.runtime.matrix.mapred.IndexedMatrixValue;
import org.apache.sysml.runtime.util.IndexRange;
import org.apache.sysml.runtime.util.UtilFunctions;

/**
 * ZeroOut with complementary=false is to zero out a subregion inside a matrix
 * ZeroOut with complementary=true is to select a subregion inside a matrix (zero out regions outside the selected range)
 */
public class ZeroOutInstruction extends UnaryMRInstructionBase {
	public IndexRange indexRange = null;
	private IndexRange tempRange = new IndexRange(-1, -1, -1, -1);
	public boolean complementary = false;

	private ZeroOutInstruction(byte in, byte out, IndexRange rng, String istr) {
		super(MRType.ZeroOut, null, in, out);
		instString = istr;
		indexRange = rng;
	}

	public static ZeroOutInstruction parseInstruction ( String str ) {
		InstructionUtils.checkNumFields ( str, 6 );
		String[] parts = InstructionUtils.getInstructionParts ( str );
		String opcode = parts[0];
		if(!opcode.equalsIgnoreCase("zeroOut"))
			throw new DMLRuntimeException("Unknown opcode while parsing a zeroout: " + str);
		byte in = Byte.parseByte(parts[1]);
		IndexRange rng=new IndexRange(UtilFunctions.parseToLong(parts[2]), 
				UtilFunctions.parseToLong(parts[3]), 
				UtilFunctions.parseToLong(parts[4]), 
				UtilFunctions.parseToLong(parts[5]));
		byte out = Byte.parseByte(parts[6]);
		return new ZeroOutInstruction(in, out, rng, str);
	}
	
	@Override
	public void processInstruction(Class<? extends MatrixValue> valueClass,
			CachedValueMap cachedValues, IndexedMatrixValue tempValue,
			IndexedMatrixValue zeroInput, int blockRowFactor, int blockColFactor) {
		ArrayList<IndexedMatrixValue> blkList = cachedValues.get(input);
		
		if( blkList != null )
			for(IndexedMatrixValue in : blkList)
			{
				if(in==null)
					continue;
			
				tempRange= UtilFunctions.getSelectedRangeForZeroOut(in, blockRowFactor, blockColFactor, indexRange);
				if(tempRange.rowStart==-1 && complementary)//just selection operation
					return;
				
				if(tempRange.rowStart==-1 && !complementary)//if no overlap, directly write them out
				{
					cachedValues.add(output, in);
					return;
				}
				
				//allocate space for the output value
				IndexedMatrixValue out;
				if(input==output)
					out=tempValue;
				else
					out=cachedValues.holdPlace(output, valueClass);
				
				//process instruction
				
				OperationsOnMatrixValues.performZeroOut(in.getIndexes(), in.getValue(), 
						out.getIndexes(), out.getValue(), tempRange, complementary);
				
				//put the output value in the cache
				if(out==tempValue)
					cachedValues.add(output, out);
			}
		
	}
}

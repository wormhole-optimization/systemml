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

import org.apache.hadoop.fs.Path;
import org.apache.hadoop.mapred.JobConf;

import org.apache.sysml.conf.ConfigurationManager;
import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.controlprogram.ParForProgramBlock.PDataPartitionFormat;
import org.apache.sysml.runtime.controlprogram.caching.MatrixObject;
import org.apache.sysml.runtime.controlprogram.context.ExecutionContext;
import org.apache.sysml.runtime.instructions.InstructionUtils;
import org.apache.sysml.runtime.io.WriterBinaryBlock;
import org.apache.sysml.runtime.matrix.MatrixCharacteristics;
import org.apache.sysml.runtime.matrix.MetaDataFormat;
import org.apache.sysml.runtime.matrix.data.InputInfo;
import org.apache.sysml.runtime.matrix.data.MatrixBlock;
import org.apache.sysml.runtime.matrix.data.OutputInfo;
import org.apache.sysml.runtime.matrix.operators.Operator;

public class DataPartitionCPInstruction extends UnaryCPInstruction {

	private final PDataPartitionFormat _pformat;

	private DataPartitionCPInstruction(Operator op, CPOperand in1, PDataPartitionFormat pformat, CPOperand out,
			String opcode, String istr) {
		super(CPType.Partition, op, in1, out, opcode, istr);
		_pformat = pformat;
	}

	public static DataPartitionCPInstruction parseInstruction ( String str ) {
		String[] parts = InstructionUtils.getInstructionPartsWithValueType(str);
		InstructionUtils.checkNumFields( parts, 3 );
		String opcode = parts[0];
		CPOperand in1 = new CPOperand(parts[1]);
		CPOperand out = new CPOperand(parts[2]);
		PDataPartitionFormat pformat = PDataPartitionFormat.valueOf(parts[3]);
		if(!opcode.equalsIgnoreCase("partition"))
			throw new DMLRuntimeException("Unknown opcode while parsing an DataPartitionCPInstruction: " + str);
		else
			return new DataPartitionCPInstruction(new Operator(true), in1, pformat, out, opcode, str);
	}
	
	@Override
	public void processInstruction(ExecutionContext ec) {
		//get input
		MatrixObject moIn = ec.getMatrixObject(input1.getName());
		MatrixBlock mb = moIn.acquireRead();
		
		//execute operations 
		MatrixObject moOut = (MatrixObject) ec.getVariable(output.getName());
		String fname = moOut.getFileName();
		moOut.setPartitioned(_pformat, -1); //modify meta data output
		try
		{
			//write matrix partitions to hdfs
			WriterBinaryBlock.writePartitionedBinaryBlockMatrixToHDFS(new Path(fname), 
				new JobConf(ConfigurationManager.getCachedJobConf()), mb, moIn.getNumRows(), moIn.getNumColumns(),
				(int)moIn.getNumRowsPerBlock(), (int)moIn.getNumColumnsPerBlock(), _pformat);
			
			//ensure correctness of output characteristics (required if input unknown during compile and no recompile)
			MatrixCharacteristics mc = new MatrixCharacteristics(moIn.getNumRows(), moIn.getNumColumns(), (int)moIn.getNumRowsPerBlock(), (int)moIn.getNumColumnsPerBlock(), moIn.getNnz()); 
			MetaDataFormat meta = new MetaDataFormat(mc, OutputInfo.BinaryBlockOutputInfo, InputInfo.BinaryBlockInputInfo);
			moOut.setMetaData(meta);
		}
		catch(Exception ex)
		{
			throw new DMLRuntimeException("Failed to execute data partitioning instruction.", ex);
		}
		
		//release input
		ec.releaseMatrixInput(input1.getName(), getExtendedOpcode());
	}
}

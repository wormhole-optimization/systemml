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

package org.apache.sysml.runtime.instructions.spark;

import org.apache.hadoop.io.LongWritable;
import org.apache.hadoop.io.Text;
import org.apache.spark.api.java.JavaPairRDD;
import org.apache.sysml.hops.recompile.Recompiler;
import org.apache.sysml.parser.Expression.DataType;
import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.controlprogram.caching.CacheableData;
import org.apache.sysml.runtime.controlprogram.caching.FrameObject;
import org.apache.sysml.runtime.controlprogram.caching.MatrixObject;
import org.apache.sysml.runtime.controlprogram.context.ExecutionContext;
import org.apache.sysml.runtime.controlprogram.context.SparkExecutionContext;
import org.apache.sysml.runtime.instructions.InstructionUtils;
import org.apache.sysml.runtime.instructions.cp.CPOperand;
import org.apache.sysml.runtime.instructions.spark.functions.ExtractBlockForBinaryReblock;
import org.apache.sysml.runtime.instructions.spark.utils.FrameRDDConverterUtils;
import org.apache.sysml.runtime.instructions.spark.utils.RDDAggregateUtils;
import org.apache.sysml.runtime.instructions.spark.utils.RDDConverterUtils;
import org.apache.sysml.runtime.matrix.MatrixCharacteristics;
import org.apache.sysml.runtime.matrix.MetaDataFormat;
import org.apache.sysml.runtime.matrix.data.CSVFileFormatProperties;
import org.apache.sysml.runtime.matrix.data.FrameBlock;
import org.apache.sysml.runtime.matrix.data.InputInfo;
import org.apache.sysml.runtime.matrix.data.MatrixBlock;
import org.apache.sysml.runtime.matrix.data.MatrixCell;
import org.apache.sysml.runtime.matrix.data.MatrixIndexes;
import org.apache.sysml.runtime.matrix.operators.Operator;

public class ReblockSPInstruction extends UnarySPInstruction {
	private int brlen;
	private int bclen;
	private boolean outputEmptyBlocks;

	private ReblockSPInstruction(Operator op, CPOperand in, CPOperand out, int br, int bc, boolean emptyBlocks,
			String opcode, String instr) {
		super(op, in, out, opcode, instr);
		brlen = br;
		bclen = bc;
		outputEmptyBlocks = emptyBlocks;
	}

	public static ReblockSPInstruction parseInstruction(String str)  throws DMLRuntimeException 
	{
		String parts[] = InstructionUtils.getInstructionPartsWithValueType(str);
		String opcode = parts[0];
		
		if(!opcode.equals("rblk")) {
			throw new DMLRuntimeException("Incorrect opcode for ReblockSPInstruction:" + opcode);
		}
		
		CPOperand in = new CPOperand(parts[1]);
		CPOperand out = new CPOperand(parts[2]);
		int brlen=Integer.parseInt(parts[3]);
		int bclen=Integer.parseInt(parts[4]);
		boolean outputEmptyBlocks = Boolean.parseBoolean(parts[5]);
		
		Operator op = null; // no operator for ReblockSPInstruction
		return new ReblockSPInstruction(op, in, out, brlen, bclen, outputEmptyBlocks, opcode, str);
	}
	

	@Override
	public void processInstruction(ExecutionContext ec)
		throws DMLRuntimeException 
	{
		SparkExecutionContext sec = (SparkExecutionContext)ec;

		//set the output characteristics
		CacheableData<?> obj = sec.getCacheableData(input1.getName());
		MatrixCharacteristics mc = sec.getMatrixCharacteristics(input1.getName());
		MatrixCharacteristics mcOut = sec.getMatrixCharacteristics(output.getName());
		mcOut.set(mc.getRows(), mc.getCols(), brlen, bclen, mc.getNonZeros());
		
		//get the source format form the meta data
		MetaDataFormat iimd = (MetaDataFormat) obj.getMetaData();
		if(iimd == null)
			throw new DMLRuntimeException("Error: Metadata not found");
		InputInfo iinfo = iimd.getInputInfo();

		//check for in-memory reblock (w/ lazy spark context, potential for latency reduction)
		if( Recompiler.checkCPReblock(sec, input1.getName()) ) {
			if( input1.getDataType() == DataType.MATRIX )
				Recompiler.executeInMemoryMatrixReblock(sec, input1.getName(), output.getName());
			else if( input1.getDataType() == DataType.FRAME )
				Recompiler.executeInMemoryFrameReblock(sec, input1.getName(), output.getName());	
			return;
		}
		
		//execute matrix/frame reblock
		if( input1.getDataType() == DataType.MATRIX )
			processMatrixReblockInstruction(sec, iinfo);
		else if( input1.getDataType() == DataType.FRAME )
			processFrameReblockInstruction(sec, iinfo);
	}

	@SuppressWarnings("unchecked")
	protected void processMatrixReblockInstruction(SparkExecutionContext sec, InputInfo iinfo) 
		throws DMLRuntimeException
	{
		MatrixObject mo = sec.getMatrixObject(input1.getName());
		MatrixCharacteristics mc = sec.getMatrixCharacteristics(input1.getName());
		MatrixCharacteristics mcOut = sec.getMatrixCharacteristics(output.getName());
		
		if(iinfo == InputInfo.TextCellInputInfo || iinfo == InputInfo.MatrixMarketInputInfo ) 
		{
			//check jdk version (prevent double.parseDouble contention on <jdk8)
			sec.checkAndRaiseValidationWarningJDKVersion();
			
			//get the input textcell rdd
			JavaPairRDD<LongWritable, Text> lines = (JavaPairRDD<LongWritable, Text>) 
					sec.getRDDHandleForVariable(input1.getName(), iinfo);
			
			//convert textcell to binary block
			JavaPairRDD<MatrixIndexes, MatrixBlock> out = 
					RDDConverterUtils.textCellToBinaryBlock(sec.getSparkContext(), lines, mcOut, outputEmptyBlocks);
			
			//put output RDD handle into symbol table
			sec.setRDDHandleForVariable(output.getName(), out);
			sec.addLineageRDD(output.getName(), input1.getName());
		}
		else if(iinfo == InputInfo.CSVInputInfo) {
			// HACK ALERT: Until we introduces the rewrite to insert csvrblock for non-persistent read
			// throw new DMLRuntimeException("CSVInputInfo is not supported for ReblockSPInstruction");
			CSVReblockSPInstruction csvInstruction = null;
			boolean hasHeader = false;
			String delim = ",";
			boolean fill = false;
			double fillValue = 0;
			if(mo.getFileFormatProperties() instanceof CSVFileFormatProperties 
			   && mo.getFileFormatProperties() != null ) 
			{
				CSVFileFormatProperties props = (CSVFileFormatProperties) mo.getFileFormatProperties();
				hasHeader = props.hasHeader();
				delim = props.getDelim();
				fill = props.isFill();
				fillValue = props.getFillValue();
			}
			
			csvInstruction = new CSVReblockSPInstruction(null, input1, output, mcOut.getRowsPerBlock(), mcOut.getColsPerBlock(), hasHeader, delim, fill, fillValue, "csvrblk", instString);
			csvInstruction.processInstruction(sec);
			return;
		}
		else if(iinfo == InputInfo.BinaryCellInputInfo) 
		{
			JavaPairRDD<MatrixIndexes, MatrixCell> binaryCells = (JavaPairRDD<MatrixIndexes, MatrixCell>) sec.getRDDHandleForVariable(input1.getName(), iinfo);
			JavaPairRDD<MatrixIndexes, MatrixBlock> out = RDDConverterUtils.binaryCellToBinaryBlock(sec.getSparkContext(), binaryCells, mcOut, outputEmptyBlocks);
			
			//put output RDD handle into symbol table
			sec.setRDDHandleForVariable(output.getName(), out);
			sec.addLineageRDD(output.getName(), input1.getName());
		}
		else if(iinfo == InputInfo.BinaryBlockInputInfo) 
		{
			//BINARY BLOCK <- BINARY BLOCK (different sizes)
			JavaPairRDD<MatrixIndexes, MatrixBlock> in1 = sec.getBinaryBlockRDDHandleForVariable(input1.getName());
			
			boolean shuffleFreeReblock = mc.dimsKnown() && mcOut.dimsKnown()
				&& (mc.getRows() < mcOut.getRowsPerBlock() || mc.getRowsPerBlock()%mcOut.getRowsPerBlock() == 0)
				&& (mc.getCols() < mcOut.getColsPerBlock() || mc.getColsPerBlock()%mcOut.getColsPerBlock() == 0);
			
			JavaPairRDD<MatrixIndexes, MatrixBlock> out = in1
				.flatMapToPair(new ExtractBlockForBinaryReblock(mc, mcOut));
			if( !shuffleFreeReblock )
				out = RDDAggregateUtils.mergeByKey(out, false);
			
			//put output RDD handle into symbol table
			sec.setRDDHandleForVariable(output.getName(), out);
			sec.addLineageRDD(output.getName(), input1.getName());
		}
		else {
			throw new DMLRuntimeException("The given InputInfo is not implemented "
					+ "for ReblockSPInstruction:" + InputInfo.inputInfoToString(iinfo));
		}
	}

	@SuppressWarnings("unchecked")
	protected void processFrameReblockInstruction(SparkExecutionContext sec, InputInfo iinfo) 
		throws DMLRuntimeException
	{
		FrameObject fo = sec.getFrameObject(input1.getName());
		MatrixCharacteristics mcOut = sec.getMatrixCharacteristics(output.getName());
		
		if(iinfo == InputInfo.TextCellInputInfo ) 
		{
			//check jdk version (prevent double.parseDouble contention on <jdk8)
			sec.checkAndRaiseValidationWarningJDKVersion();
			
			//get the input textcell rdd
			JavaPairRDD<LongWritable, Text> lines = (JavaPairRDD<LongWritable, Text>) 
					sec.getRDDHandleForVariable(input1.getName(), iinfo);
			
			//convert textcell to binary block
			JavaPairRDD<Long, FrameBlock> out = 
					FrameRDDConverterUtils.textCellToBinaryBlock(sec.getSparkContext(), lines, mcOut, fo.getSchema());
			
			//put output RDD handle into symbol table
			sec.setRDDHandleForVariable(output.getName(), out);
			sec.addLineageRDD(output.getName(), input1.getName());
		}
		else if(iinfo == InputInfo.CSVInputInfo) {
			// HACK ALERT: Until we introduces the rewrite to insert csvrblock for non-persistent read
			// throw new DMLRuntimeException("CSVInputInfo is not supported for ReblockSPInstruction");
			CSVReblockSPInstruction csvInstruction = null;
			boolean hasHeader = false;
			String delim = ",";
			boolean fill = false;
			double fillValue = 0;
			if(fo.getFileFormatProperties() instanceof CSVFileFormatProperties 
			   && fo.getFileFormatProperties() != null ) 
			{
				CSVFileFormatProperties props = (CSVFileFormatProperties) fo.getFileFormatProperties();
				hasHeader = props.hasHeader();
				delim = props.getDelim();
				fill = props.isFill();
				fillValue = props.getFillValue();
			}
			
			csvInstruction = new CSVReblockSPInstruction(null, input1, output, mcOut.getRowsPerBlock(), mcOut.getColsPerBlock(), hasHeader, delim, fill, fillValue, "csvrblk", instString);
			csvInstruction.processInstruction(sec);
		}
		else {
			throw new DMLRuntimeException("The given InputInfo is not implemented "
					+ "for ReblockSPInstruction: " + InputInfo.inputInfoToString(iinfo));
		}
	}
}

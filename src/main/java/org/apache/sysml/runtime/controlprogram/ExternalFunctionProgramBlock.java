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

package org.apache.sysml.runtime.controlprogram;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.StringTokenizer;
import java.util.TreeMap;

import org.apache.sysml.api.DMLScript;
import org.apache.sysml.conf.ConfigurationManager;
import org.apache.sysml.lops.Lop;
import org.apache.sysml.lops.ReBlock;
import org.apache.sysml.lops.compile.JobType;
import org.apache.sysml.parser.DataIdentifier;
import org.apache.sysml.parser.Expression.DataType;
import org.apache.sysml.parser.Expression.ValueType;
import org.apache.sysml.parser.ExternalFunctionStatement;
import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.controlprogram.caching.CacheException;
import org.apache.sysml.runtime.controlprogram.caching.MatrixObject;
import org.apache.sysml.runtime.controlprogram.context.ExecutionContext;
import org.apache.sysml.runtime.controlprogram.parfor.util.IDSequence;
import org.apache.sysml.runtime.instructions.Instruction;
import org.apache.sysml.runtime.instructions.MRJobInstruction;
import org.apache.sysml.runtime.instructions.cp.BooleanObject;
import org.apache.sysml.runtime.instructions.cp.Data;
import org.apache.sysml.runtime.instructions.cp.DoubleObject;
import org.apache.sysml.runtime.instructions.cp.IntObject;
import org.apache.sysml.runtime.instructions.cp.ScalarObject;
import org.apache.sysml.runtime.instructions.cp.StringObject;
import org.apache.sysml.runtime.instructions.cp.VariableCPInstruction;
import org.apache.sysml.runtime.matrix.MatrixCharacteristics;
import org.apache.sysml.runtime.matrix.MatrixFormatMetaData;
import org.apache.sysml.runtime.matrix.data.InputInfo;
import org.apache.sysml.runtime.matrix.data.OutputInfo;
import org.apache.sysml.udf.ExternalFunctionInvocationInstruction;
import org.apache.sysml.udf.FunctionParameter;
import org.apache.sysml.udf.Matrix;
import org.apache.sysml.udf.PackageFunction;
import org.apache.sysml.udf.Scalar;
import org.apache.sysml.udf.FunctionParameter.FunctionParameterType;
import org.apache.sysml.udf.BinaryObject;
import org.apache.sysml.udf.Scalar.ScalarValueType;

public class ExternalFunctionProgramBlock extends FunctionProgramBlock 
{
		
	protected static final IDSequence _idSeq = new IDSequence();

	protected String _baseDir = null;

	ArrayList<Instruction> block2CellInst; 
	ArrayList<Instruction> cell2BlockInst; 

	// holds other key value parameters specified in function declaration
	protected HashMap<String, String> _otherParams;

	protected HashMap<String, String> _unblockedFileNames;
	protected HashMap<String, String> _blockedFileNames;

	protected long _runID = -1; //ID for block of statements
	
	/**
	 * Constructor that also provides otherParams that are needed for external
	 * functions. Remaining parameters will just be passed to constructor for
	 * function program block.
	 * 
	 * @param prog runtime program
	 * @param inputParams list of input data identifiers
	 * @param outputParams list of output data indentifiers
	 * @param baseDir base directory
	 * @throws DMLRuntimeException if DMLRuntimeException occurs
	 */
	protected ExternalFunctionProgramBlock(Program prog,
			ArrayList<DataIdentifier> inputParams,
			ArrayList<DataIdentifier> outputParams,
			String baseDir) throws DMLRuntimeException
	{
		super(prog, inputParams, outputParams);		
		_baseDir = baseDir;
	}
	
	public ExternalFunctionProgramBlock(Program prog,
			ArrayList<DataIdentifier> inputParams,
			ArrayList<DataIdentifier> outputParams,
			HashMap<String, String> otherParams,
			String baseDir) throws DMLRuntimeException {

		super(prog, inputParams, outputParams);
		_baseDir = baseDir;
		
		// copy other params
		_otherParams = new HashMap<String, String>();
		_otherParams.putAll(otherParams);

		_unblockedFileNames = new HashMap<String, String>();
		_blockedFileNames = new HashMap<String, String>();
	
		// generate instructions
		createInstructions();
	}
	
	private void changeTmpInput( long id, ExecutionContext ec )
	{
		ArrayList<DataIdentifier> inputParams = getInputParams();
		block2CellInst = getBlock2CellInstructions(inputParams, _unblockedFileNames);
		
		//post processing FUNCTION PATCH
		for( String var : _skipInReblock )
		{
			Data dat = ec.getVariable(var);
			if( dat instanceof MatrixObject )
				_unblockedFileNames.put(var, ((MatrixObject)dat).getFileName());
		}
	}
	
	/**
	 * It is necessary to change the local temporary files as only file handles are passed out
	 * by the external function program block.
	 * 
	 * 
	 * @param id this field does nothing
	 */
	private void changeTmpOutput( long id )
	{
		ArrayList<DataIdentifier> outputParams = getOutputParams();
		cell2BlockInst = getCell2BlockInstructions(outputParams, _blockedFileNames);
	}

	public String getBaseDir()
	{
		return _baseDir;
	}
	
	/**
	 * Method to be invoked to execute instructions for the external function
	 * invocation
	 */
	@Override
	public void execute(ExecutionContext ec) 
		throws DMLRuntimeException
	{
		_runID = _idSeq.getNextID();
		
		changeTmpInput( _runID, ec ); 
		changeTmpOutput( _runID );
		
		// export input variables to HDFS (see RunMRJobs)
		ArrayList<DataIdentifier> inputParams = null;
		
		try {
			inputParams = getInputParams();
			for(DataIdentifier di : inputParams ) {			
				Data d = ec.getVariable(di.getName());
				if ( d.getDataType() == DataType.MATRIX ) {
					MatrixObject inputObj = (MatrixObject) d;
					inputObj.exportData();
				}
			}
		}
		catch (Exception e){
			throw new DMLRuntimeException(this.printBlockErrorLocation() + "Error exporting input variables to HDFS", e);
		}
		
		// convert block to cell
		if( block2CellInst != null )
		{
			ArrayList<Instruction> tempInst = new ArrayList<Instruction>();
			tempInst.addAll(block2CellInst);
			try {
				this.executeInstructions(tempInst,ec);
			} catch (Exception e) {
				
				throw new DMLRuntimeException(this.printBlockErrorLocation() + "Error executing "
						+ tempInst.toString(), e);
			}
		}
		
		// now execute package function
		for (int i = 0; i < _inst.size(); i++) 
		{
			try {
				if (_inst.get(i) instanceof ExternalFunctionInvocationInstruction)
					executeInstruction(ec, (ExternalFunctionInvocationInstruction) _inst.get(i));
			} 
			catch(Exception e) {
				throw new DMLRuntimeException(this.printBlockErrorLocation() + 
						"Failed to execute instruction " + _inst.get(i).toString(), e);
			}
		}

		// convert cell to block
		if( cell2BlockInst != null )
		{
			ArrayList<Instruction> tempInst = new ArrayList<Instruction>();
			try {
				tempInst.clear();
				tempInst.addAll(cell2BlockInst);
				this.executeInstructions(tempInst, ec);
			} catch (Exception e) {
				
				throw new DMLRuntimeException(this.printBlockErrorLocation() + "Failed to execute instruction "
						+ cell2BlockInst.toString(), e);
			}
		}
		
		// check return values
		checkOutputParameters(ec.getVariables());
	}

	/**
	 * Given a list of parameters as data identifiers, returns a string
	 * representation.
	 * 
	 * @param params list of data identifiers
	 * @return parameter string
	 */
	protected String getParameterString(ArrayList<DataIdentifier> params) {
		String parameterString = "";

		for (int i = 0; i < params.size(); i++) {
			if (i != 0)
				parameterString += ",";

			DataIdentifier param = params.get(i);

			if (param.getDataType() == DataType.MATRIX) {
				String s = getDataTypeString(DataType.MATRIX) + ":";
				s = s + "" + param.getName() + "" + ":";
				s = s + getValueTypeString(param.getValueType());
				parameterString += s;
				continue;
			}

			if (param.getDataType() == DataType.SCALAR) {
				String s = getDataTypeString(DataType.SCALAR) + ":";
				s = s + "" + param.getName() + "" + ":";
				s = s + getValueTypeString(param.getValueType());
				parameterString += s;
				continue;
			}

			if (param.getDataType() == DataType.OBJECT) {
				String s = getDataTypeString(DataType.OBJECT) + ":";
				s = s + "" + param.getName() + "" + ":";
				parameterString += s;
				continue;
			}
		}

		return parameterString;
	}

	/**
	 * method to create instructions
	 */
	protected void createInstructions() {

		_inst = new ArrayList<Instruction>();

		// unblock all input matrices
		block2CellInst = getBlock2CellInstructions(getInputParams(),_unblockedFileNames);

		// assemble information provided through keyvalue pairs
		String className = _otherParams.get(ExternalFunctionStatement.CLASS_NAME);
		String configFile = _otherParams.get(ExternalFunctionStatement.CONFIG_FILE);
		
		// class name cannot be null, however, configFile and execLocation can
		// be null
		if (className == null)
			throw new RuntimeException(this.printBlockErrorLocation() + ExternalFunctionStatement.CLASS_NAME + " not provided!");

		// assemble input and output param strings
		String inputParameterString = getParameterString(getInputParams());
		String outputParameterString = getParameterString(getOutputParams());

		// generate instruction
		ExternalFunctionInvocationInstruction einst = new ExternalFunctionInvocationInstruction(
				className, configFile, inputParameterString,
				outputParameterString);
		
		if (getInputParams().size() > 0)
			einst.setLocation(getInputParams().get(0));
		else if (getOutputParams().size() > 0)
			einst.setLocation(getOutputParams().get(0));
		else
			einst.setLocation(this.getFilename(), this._beginLine, this._endLine, this._beginColumn, this._endColumn);
		
		_inst.add(einst);

		// block output matrices
		cell2BlockInst = getCell2BlockInstructions(getOutputParams(),_blockedFileNames);
	}

	
	/**
	 * Method to generate a reblock job to convert the cell representation into block representation
	 * 
	 * @param outputParams list out output data identifiers
	 * @param blockedFileNames map of blocked file names
	 * @return list of instructions
	 */
	private ArrayList<Instruction> getCell2BlockInstructions(
			ArrayList<DataIdentifier> outputParams,
			HashMap<String, String> blockedFileNames) {
		
		ArrayList<Instruction> c2binst = null;
		
		//list of matrices that need to be reblocked
		ArrayList<DataIdentifier> matrices = new ArrayList<DataIdentifier>();
		ArrayList<DataIdentifier> matricesNoReblock = new ArrayList<DataIdentifier>();

		// identify outputs that are matrices
		for (int i = 0; i < outputParams.size(); i++) {
			if (outputParams.get(i).getDataType() == DataType.MATRIX) {
				if( _skipOutReblock.contains(outputParams.get(i).getName()) )
					matricesNoReblock.add(outputParams.get(i));
				else
					matrices.add(outputParams.get(i));
			}
		}

		if( !matrices.isEmpty() )
		{
			c2binst = new ArrayList<Instruction>();
			MRJobInstruction reblkInst = new MRJobInstruction(JobType.REBLOCK);
			TreeMap<Integer, ArrayList<String>> MRJobLineNumbers = null;
			if(DMLScript.ENABLE_DEBUG_MODE) {
				MRJobLineNumbers = new TreeMap<Integer, ArrayList<String>>();
			}
			
			ArrayList<String> inLabels = new ArrayList<String>();
			ArrayList<String> outLabels = new ArrayList<String>();
			String[] outputs = new String[matrices.size()];
			byte[] resultIndex = new byte[matrices.size()];
			String reblock = "";
			String reblockStr = ""; //Keep a copy of a single MR reblock instruction
	
			String scratchSpaceLoc = ConfigurationManager.getScratchSpace();
			
			try {
				// create a RBLK job that transforms each output matrix from cell to block
				for (int i = 0; i < matrices.size(); i++) {
					inLabels.add(matrices.get(i).getName());
					outLabels.add(matrices.get(i).getName() + "_extFnOutput");
					outputs[i] = scratchSpaceLoc +
					             Lop.FILE_SEPARATOR + Lop.PROCESS_PREFIX + DMLScript.getUUID() + Lop.FILE_SEPARATOR + 
		                         _otherParams.get(ExternalFunctionStatement.CLASS_NAME) + _runID + "_" + i + "Output";
					blockedFileNames.put(matrices.get(i).getName(), outputs[i]);
					resultIndex[i] = (byte) i; // (matrices.size()+i);
		
					if (i > 0)
						reblock += Lop.INSTRUCTION_DELIMITOR;
		
					reblock += "MR" + ReBlock.OPERAND_DELIMITOR + "rblk" + ReBlock.OPERAND_DELIMITOR + 
									i + ReBlock.DATATYPE_PREFIX + matrices.get(i).getDataType() + ReBlock.VALUETYPE_PREFIX + matrices.get(i).getValueType() + ReBlock.OPERAND_DELIMITOR + 
									i + ReBlock.DATATYPE_PREFIX + matrices.get(i).getDataType() + ReBlock.VALUETYPE_PREFIX + matrices.get(i).getValueType() + ReBlock.OPERAND_DELIMITOR + 
									ConfigurationManager.getBlocksize() + ReBlock.OPERAND_DELIMITOR + ConfigurationManager.getBlocksize() + ReBlock.OPERAND_DELIMITOR + "true";
					
					if(DMLScript.ENABLE_DEBUG_MODE) {
						//Create a copy of reblock instruction but as a single instruction (FOR DEBUGGER)
						reblockStr = "MR" + ReBlock.OPERAND_DELIMITOR + "rblk" + ReBlock.OPERAND_DELIMITOR + 
										i + ReBlock.DATATYPE_PREFIX + matrices.get(i).getDataType() + ReBlock.VALUETYPE_PREFIX + matrices.get(i).getValueType() + ReBlock.OPERAND_DELIMITOR + 
										i + ReBlock.DATATYPE_PREFIX + matrices.get(i).getDataType() + ReBlock.VALUETYPE_PREFIX + matrices.get(i).getValueType() + ReBlock.OPERAND_DELIMITOR + 
										ConfigurationManager.getBlocksize() + ReBlock.OPERAND_DELIMITOR + ConfigurationManager.getBlocksize()  + ReBlock.OPERAND_DELIMITOR + "true";					
						//Set MR reblock instruction line number (FOR DEBUGGER)
						if (!MRJobLineNumbers.containsKey(matrices.get(i).getBeginLine())) {
							MRJobLineNumbers.put(matrices.get(i).getBeginLine(), new ArrayList<String>()); 
						}
						MRJobLineNumbers.get(matrices.get(i).getBeginLine()).add(reblockStr);					
					}
					// create metadata instructions to populate symbol table 
					// with variables that hold blocked matrices
					Instruction createInst = VariableCPInstruction.prepareCreateMatrixVariableInstruction(outLabels.get(i), outputs[i], false, OutputInfo.outputInfoToString(OutputInfo.BinaryBlockOutputInfo));
					createInst.setLocation(matrices.get(i));
					
					c2binst.add(createInst);

				}
		
				reblkInst.setReBlockInstructions(inLabels.toArray(new String[inLabels.size()]), "", reblock, "", 
						outLabels.toArray(new String[inLabels.size()]), resultIndex, 1, 1);
				c2binst.add(reblkInst);
		
				// generate instructions that rename the output variables of REBLOCK job
				Instruction cpInst = null, rmInst = null;
				for (int i = 0; i < matrices.size(); i++) {
					cpInst = VariableCPInstruction.prepareCopyInstruction(outLabels.get(i), matrices.get(i).getName());
					rmInst = VariableCPInstruction.prepareRemoveInstruction(outLabels.get(i));
					
					cpInst.setLocation(matrices.get(i));
					rmInst.setLocation(matrices.get(i));
					
					c2binst.add(cpInst);
					c2binst.add(rmInst);
					//c2binst.add(CPInstructionParser.parseSingleInstruction("CP" + Lops.OPERAND_DELIMITOR + "cpvar"+Lops.OPERAND_DELIMITOR+ outLabels.get(i) + Lops.OPERAND_DELIMITOR + matrices.get(i).getName()));
				}
			} catch (Exception e) {
				throw new RuntimeException(this.printBlockErrorLocation() + "error generating instructions", e);
			}
			
			//LOGGING instructions
			if (LOG.isTraceEnabled()){
				LOG.trace("\n--- Cell-2-Block Instructions ---");
				for(Instruction i : c2binst) {
					LOG.trace(i.toString());
				}
				LOG.trace("----------------------------------");
			}
			
		}
		
		return c2binst; //null if no output matrices
	}

	/**
	 * Method to generate instructions to convert input matrices from block to
	 * cell. We generate a GMR job here.
	 * 
	 * @param inputParams list of data identifiers
	 * @param unBlockedFileNames map of unblocked file names
	 * @return list of instructions
	 */
	private ArrayList<Instruction> getBlock2CellInstructions(
			ArrayList<DataIdentifier> inputParams,
			HashMap<String, String> unBlockedFileNames) {
		
		ArrayList<Instruction> b2cinst = null;
		
		//list of input matrices
		ArrayList<DataIdentifier> matrices = new ArrayList<DataIdentifier>();
		ArrayList<DataIdentifier> matricesNoReblock = new ArrayList<DataIdentifier>();

		// find all inputs that are matrices
		for (int i = 0; i < inputParams.size(); i++) {
			if (inputParams.get(i).getDataType() == DataType.MATRIX) {
				if( _skipInReblock.contains(inputParams.get(i).getName()) )
					matricesNoReblock.add(inputParams.get(i));
				else
					matrices.add(inputParams.get(i));
			}
		}
		
		if( !matrices.isEmpty() )
		{
			b2cinst = new ArrayList<Instruction>();
			MRJobInstruction gmrInst = new MRJobInstruction(JobType.GMR);
			TreeMap<Integer, ArrayList<String>> MRJobLineNumbers = null;
			if(DMLScript.ENABLE_DEBUG_MODE) {
				MRJobLineNumbers = new TreeMap<Integer, ArrayList<String>>();
			}
			String gmrStr="";
			ArrayList<String> inLabels = new ArrayList<String>();
			ArrayList<String> outLabels = new ArrayList<String>();
			String[] outputs = new String[matrices.size()];
			byte[] resultIndex = new byte[matrices.size()];
	
			String scratchSpaceLoc = ConfigurationManager.getScratchSpace();
			
			
			try {
				// create a GMR job that transforms each of these matrices from block to cell
				for (int i = 0; i < matrices.size(); i++) {
					
					inLabels.add(matrices.get(i).getName());
					outLabels.add(matrices.get(i).getName()+"_extFnInput");
					resultIndex[i] = (byte) i; //(matrices.size()+i);
	
					outputs[i] = scratchSpaceLoc +
									Lop.FILE_SEPARATOR + Lop.PROCESS_PREFIX + DMLScript.getUUID() + Lop.FILE_SEPARATOR + 
									_otherParams.get(ExternalFunctionStatement.CLASS_NAME) + _runID + "_" + i + "Input";
					unBlockedFileNames.put(matrices.get(i).getName(), outputs[i]);
	
					if(DMLScript.ENABLE_DEBUG_MODE) {
						//Create a dummy gmr instruction (FOR DEBUGGER)
						gmrStr = "MR" + Lop.OPERAND_DELIMITOR + "gmr" + Lop.OPERAND_DELIMITOR + 
										i + Lop.DATATYPE_PREFIX + matrices.get(i).getDataType() + Lop.VALUETYPE_PREFIX + matrices.get(i).getValueType() + Lop.OPERAND_DELIMITOR + 
										i + Lop.DATATYPE_PREFIX + matrices.get(i).getDataType() + Lop.VALUETYPE_PREFIX + matrices.get(i).getValueType() + Lop.OPERAND_DELIMITOR + 
										ConfigurationManager.getBlocksize() + Lop.OPERAND_DELIMITOR + ConfigurationManager.getBlocksize();
						
						//Set MR gmr instruction line number (FOR DEBUGGER)
						if (!MRJobLineNumbers.containsKey(matrices.get(i).getBeginLine())) {
							MRJobLineNumbers.put(matrices.get(i).getBeginLine(), new ArrayList<String>()); 
						}
						MRJobLineNumbers.get(matrices.get(i).getBeginLine()).add(gmrStr);
					}
					// create metadata instructions to populate symbol table 
					// with variables that hold unblocked matrices
				 	Instruction createInst = VariableCPInstruction.prepareCreateMatrixVariableInstruction(outLabels.get(i), outputs[i], false, OutputInfo.outputInfoToString(OutputInfo.TextCellOutputInfo));			 		
			 		createInst.setLocation(matrices.get(i));
			 		
			 		b2cinst.add(createInst);
				}
			
				// Finally, generate GMR instruction that performs block2cell conversion
				gmrInst.setGMRInstructions(inLabels.toArray(new String[inLabels.size()]), "", "", "", "", 
						outLabels.toArray(new String[outLabels.size()]), resultIndex, 0, 1);
				
				b2cinst.add(gmrInst);
			
				// generate instructions that rename the output variables of GMR job
				Instruction cpInst=null, rmInst=null;
				for (int i = 0; i < matrices.size(); i++) {
						cpInst = VariableCPInstruction.prepareCopyInstruction(outLabels.get(i), matrices.get(i).getName());
						rmInst = VariableCPInstruction.prepareRemoveInstruction(outLabels.get(i));
						
						cpInst.setLocation(matrices.get(i));
						rmInst.setLocation(matrices.get(i));
						
						b2cinst.add(cpInst);
						b2cinst.add(rmInst);
				}
			} catch (Exception e) {
				throw new RuntimeException(e);
			}
		
			//LOG instructions
			if (LOG.isTraceEnabled()){
				LOG.trace("\n--- Block-2-Cell Instructions ---");
				for(Instruction i : b2cinst) {
					LOG.trace(i.toString());
				}
				LOG.trace("----------------------------------");
			}			
		}
		
		//BEGIN FUNCTION PATCH
		if( !matricesNoReblock.isEmpty() )
		{	
			for( int i=0; i<matricesNoReblock.size(); i++ )
			{
				String scratchSpaceLoc = ConfigurationManager.getScratchSpace();
				String filename = scratchSpaceLoc +
							          Lop.FILE_SEPARATOR + Lop.PROCESS_PREFIX + DMLScript.getUUID() + Lop.FILE_SEPARATOR + 
							           _otherParams.get(ExternalFunctionStatement.CLASS_NAME) + _runID + "_" + i + "Input";
				unBlockedFileNames.put(matricesNoReblock.get(i).getName(), filename); 			
			}
		}
		//END FUNCTION PATCH
		
		return b2cinst; //null if no input matrices
	}

	/**
	 * Method to execute an external function invocation instruction.
	 * 
	 * @param ec execution context
	 * @param inst external function invocation instructions
	 * @throws DMLRuntimeException if DMLRuntimeException occurs
	 */
	@SuppressWarnings("unchecked")
	public void executeInstruction(ExecutionContext ec, ExternalFunctionInvocationInstruction inst) 
		throws DMLRuntimeException 
	{		
		String className = inst.getClassName();
		String configFile = inst.getConfigFile();

		if (className == null)
			throw new DMLRuntimeException(this.printBlockErrorLocation() + "Class name can't be null");

		// create instance of package function.
		Object o;
		try 
		{
			Class<Instruction> cla = (Class<Instruction>) Class.forName(className);
			o = cla.newInstance();
		} 
		catch (Exception e) 
		{
			throw new DMLRuntimeException(this.printBlockErrorLocation() + "Error generating package function object " ,e );
		}

		if (!(o instanceof PackageFunction))
			throw new DMLRuntimeException(this.printBlockErrorLocation() + "Class is not of type PackageFunction");

		PackageFunction func = (PackageFunction) o;

		// add inputs to this package function based on input parameter
		// and their mappings.
		setupInputs(func, inst.getInputParams(), ec.getVariables());
		func.setConfiguration(configFile);
		func.setBaseDir(_baseDir);
		
		//executes function
		func.execute();
		
		// verify output of function execution matches declaration
		// and add outputs to variableMapping and Metadata
		verifyAndAttachOutputs(ec, func, inst.getOutputParams());
	}

	/**
	 * Method to verify that function outputs match with declared outputs
	 * 
	 * @param ec execution context
	 * @param returnFunc package function
	 * @param outputParams output parameters
	 * @throws DMLRuntimeException if DMLRuntimeException occurs
	 */
	protected void verifyAndAttachOutputs(ExecutionContext ec, PackageFunction returnFunc,
			String outputParams) throws DMLRuntimeException {

		ArrayList<String> outputs = getParameters(outputParams);
		// make sure they are of equal size first

		if (outputs.size() != returnFunc.getNumFunctionOutputs()) {
			throw new DMLRuntimeException(
					"Number of function outputs ("+returnFunc.getNumFunctionOutputs()+") " +
					"does not match with declaration ("+outputs.size()+").");
		}

		// iterate over each output and verify that type matches
		for (int i = 0; i < outputs.size(); i++) {
			StringTokenizer tk = new StringTokenizer(outputs.get(i), ":");
			ArrayList<String> tokens = new ArrayList<String>();
			while (tk.hasMoreTokens()) {
				tokens.add(tk.nextToken());
			}

			if (returnFunc.getFunctionOutput(i).getType() == FunctionParameterType.Matrix) {
				Matrix m = (Matrix) returnFunc.getFunctionOutput(i);

				if (!(tokens.get(0).equals(getFunctionParameterDataTypeString(FunctionParameterType.Matrix)))
						|| !(tokens.get(2).equals(getMatrixValueTypeString(m.getValueType())))) {
					throw new DMLRuntimeException(
							"Function output '"+outputs.get(i)+"' does not match with declaration.");
				}

				// add result to variableMapping
				String varName = tokens.get(1);
				MatrixObject newVar = createOutputMatrixObject( m ); 
				newVar.setVarName(varName);
				
				//getVariables().put(varName, newVar); //put/override in local symbol table
				ec.setVariable(varName, newVar);
				
				continue;
			}

			if (returnFunc.getFunctionOutput(i).getType() == FunctionParameterType.Scalar) {
				Scalar s = (Scalar) returnFunc.getFunctionOutput(i);

				if (!tokens.get(0).equals(getFunctionParameterDataTypeString(FunctionParameterType.Scalar))
						|| !tokens.get(2).equals(
								getScalarValueTypeString(s.getScalarType()))) {
					throw new DMLRuntimeException(
							"Function output '"+outputs.get(i)+"' does not match with declaration.");
				}

				// allocate and set appropriate object based on type
				ScalarObject scalarObject = null;
				ScalarValueType type = s.getScalarType();
				switch (type) {
				case Integer:
					scalarObject = new IntObject(tokens.get(1),
							Long.parseLong(s.getValue()));
					break;
				case Double:
					scalarObject = new DoubleObject(tokens.get(1),
							Double.parseDouble(s.getValue()));
					break;
				case Boolean:
					scalarObject = new BooleanObject(tokens.get(1),
							Boolean.parseBoolean(s.getValue()));
					break;
				case Text:
					scalarObject = new StringObject(tokens.get(1), s.getValue());
					break;
				default:
					throw new DMLRuntimeException(
							"Unknown scalar value type '"+type+"' of output '"+outputs.get(i)+"'.");
				}

				//this.getVariables().put(tokens.get(1), scalarObject);
				ec.setVariable(tokens.get(1), scalarObject);
				continue;
			}

			if (returnFunc.getFunctionOutput(i).getType() == FunctionParameterType.Object) {
				if (!tokens.get(0).equals(getFunctionParameterDataTypeString(FunctionParameterType.Object))) {
					throw new DMLRuntimeException(
							"Function output '"+outputs.get(i)+"' does not match with declaration.");
				}

				throw new DMLRuntimeException(
						"Object types not yet supported");

				// continue;
			}

			throw new DMLRuntimeException(
					"Unknown data type '"+returnFunc.getFunctionOutput(i).getType()+"' " +
					"of output '"+outputs.get(i)+"'.");
		}
	}

	protected MatrixObject createOutputMatrixObject( Matrix m ) 
		throws CacheException 
	{
		MatrixCharacteristics mc = new MatrixCharacteristics(m.getNumRows(),m.getNumCols(), ConfigurationManager.getBlocksize(), ConfigurationManager.getBlocksize());
		MatrixFormatMetaData mfmd = new MatrixFormatMetaData(mc, OutputInfo.TextCellOutputInfo, InputInfo.TextCellInputInfo);		
		return new MatrixObject(ValueType.DOUBLE, m.getFilePath(), mfmd);
	}

	/**
	 * Method to get string representation of scalar value type
	 * 
	 * @param scalarType scalar value type
	 * @return scalar value type string
	 */
	protected String getScalarValueTypeString(ScalarValueType scalarType) {
		if (scalarType.equals(ScalarValueType.Text))
			return "String";
		else
			return scalarType.toString();
	}

	/**
	 * Method to parse inputs, update labels, and add to package function.
	 * 
	 * @param func package function
	 * @param inputParams input parameters
	 * @param variableMapping local variable map
	 */
	protected void setupInputs (PackageFunction func, String inputParams, LocalVariableMap variableMapping) {
		ArrayList<String> inputs = getParameters(inputParams);
		ArrayList<FunctionParameter> inputObjects = getInputObjects(inputs, variableMapping);
		func.setNumFunctionInputs(inputObjects.size());
		for (int i = 0; i < inputObjects.size(); i++)
			func.setInput(inputObjects.get(i), i);
	}

	/**
	 * Method to convert string representation of input into function input
	 * object.
	 * 
	 * @param inputs list of inputs
	 * @param variableMapping local variable map
	 * @return list of function parameters
	 */
	protected ArrayList<FunctionParameter> getInputObjects(ArrayList<String> inputs,
			LocalVariableMap variableMapping) {
		ArrayList<FunctionParameter> inputObjects = new ArrayList<FunctionParameter>();

		for (int i = 0; i < inputs.size(); i++) {
			ArrayList<String> tokens = new ArrayList<String>();
			StringTokenizer tk = new StringTokenizer(inputs.get(i), ":");
			while (tk.hasMoreTokens()) {
				tokens.add(tk.nextToken());
			}

			if (tokens.get(0).equals("Matrix")) {
				String varName = tokens.get(1);
				MatrixObject mobj = (MatrixObject) variableMapping.get(varName);
				MatrixCharacteristics mc = mobj.getMatrixCharacteristics();
				Matrix m = new Matrix(mobj.getFileName(),
						mc.getRows(), mc.getCols(),
						getMatrixValueType(tokens.get(2)));
				modifyInputMatrix(m, mobj);
				inputObjects.add(m);
			}

			if (tokens.get(0).equals("Scalar")) {
				String varName = tokens.get(1);
				ScalarObject so = (ScalarObject) variableMapping.get(varName);
				Scalar s = new Scalar(getScalarValueType(tokens.get(2)),
						so.getStringValue());
				inputObjects.add(s);

			}

			if (tokens.get(0).equals("Object")) {
				String varName = tokens.get(1);
				Object o = variableMapping.get(varName);
				BinaryObject obj = new BinaryObject(o);
				inputObjects.add(obj);

			}
		}

		return inputObjects;

	}

	protected void modifyInputMatrix(Matrix m, MatrixObject mobj) 
	{
		//do nothing, intended for extensions
	}

	/**
	 * Converts string representation of scalar value type to enum type
	 * 
	 * @param string scalar value string
	 * @return scalar value type
	 */
	protected ScalarValueType getScalarValueType(String string) {
		if (string.equals("String"))
			return ScalarValueType.Text;
		else 
			return ScalarValueType.valueOf(string);
	}

	/**
	 * Get string representation of matrix value type
	 * 
	 * @param t matrix value type
	 * @return matrix value type as string
	 */
	protected String getMatrixValueTypeString(Matrix.ValueType t) {
		return t.toString();
	}

	/**
	 * Converts string representation of matrix value type into enum type
	 * 
	 * @param string matrix value type as string
	 * @return matrix value type
	 */
	protected Matrix.ValueType getMatrixValueType(String string) {
		return Matrix.ValueType.valueOf(string); 
	}

	/**
	 * Method to break the comma separated input parameters into an arraylist of
	 * parameters
	 * 
	 * @param inputParams input parameters
	 * @return list of string inputs
	 */
	protected ArrayList<String> getParameters(String inputParams) {
		ArrayList<String> inputs = new ArrayList<String>();

		StringTokenizer tk = new StringTokenizer(inputParams, ",");
		while (tk.hasMoreTokens()) {
			inputs.add(tk.nextToken());
		}

		return inputs;
	}

	/**
	 * Get string representation for data type
	 * 
	 * @param d data type
	 * @return string representation of data type
	 */
	protected String getDataTypeString(DataType d) {
		if (d.equals(DataType.MATRIX))
			return "Matrix";

		if (d.equals(DataType.SCALAR))
			return "Scalar";

		if (d.equals(DataType.OBJECT))
			return "Object";

		throw new RuntimeException("Should never come here");
	}

	/**
	 * Method to get string representation of function parameter type.
	 * 
	 * @param t function parameter type
	 * @return function parameter type as string
	 */
	protected String getFunctionParameterDataTypeString(FunctionParameterType t) {
		return t.toString();
	}

	/**
	 * Get string representation of value type
	 * 
	 * @param v value type
	 * @return value type string
	 */
	protected String getValueTypeString(ValueType v) {
		if (v.equals(ValueType.DOUBLE))
			return "Double";

		if (v.equals(ValueType.INT))
			return "Integer";

		if (v.equals(ValueType.BOOLEAN))
			return "Boolean";

		if (v.equals(ValueType.STRING))
			return "String";

		throw new RuntimeException("Should never come here");
	}

	public HashMap<String,String> getOtherParams() {
		return _otherParams;
	}
	
	public String printBlockErrorLocation(){
		return "ERROR: Runtime error in external function program block generated from external function statement block between lines " + _beginLine + " and " + _endLine + " -- ";
	}
	
	
	/////////////////////////////////////////////////
	// Extension for Global Data Flow Optimization
	// by Mathias Peters
	///////
	
	//FUNCTION PATCH
	
	private Collection<String> _skipInReblock = new HashSet<String>();
	private Collection<String> _skipOutReblock = new HashSet<String>();
	
	@Override
	public ArrayList<Instruction> getInstructions()
	{
		ArrayList<Instruction> tmp = new ArrayList<Instruction>();
		if( cell2BlockInst != null )
			tmp.addAll(cell2BlockInst);
		if( block2CellInst != null )
			tmp.addAll(block2CellInst);
		return tmp;
	}
}
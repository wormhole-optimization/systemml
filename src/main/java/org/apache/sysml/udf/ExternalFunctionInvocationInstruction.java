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

package org.apache.sysml.udf;

import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.controlprogram.context.ExecutionContext;
import org.apache.sysml.runtime.instructions.Instruction;

/**
 * Class to maintain external function invocation instructions.
 * 
 * 
 * 
 */
public class ExternalFunctionInvocationInstruction extends Instruction 
{
	
	public static final String ELEMENT_DELIM = ":";
	
	public String _namespace;
	public String _functionName;
	protected String className; // name of class that contains the function
	protected String configFile; // optional configuration file parameter
	protected String inputParams; // string representation of input parameters
	protected String outputParams; // string representation of output parameters
	
	public ExternalFunctionInvocationInstruction(String className,
			String configFile, String inputParams,
			String outputParams) 
	{
		this.className = className;
		this.configFile = configFile;
		this.inputParams = inputParams;
		this.outputParams = outputParams;
	}
	
	public String getClassName() {
		return className;
	}

	public String getConfigFile() {
		return configFile;
	}

	public String getInputParams() {
		return inputParams;
	}

	public String getOutputParams() {
		return outputParams;
	}

	@Override
	public String toString() {
		return className + ELEMENT_DELIM + 
			configFile + ELEMENT_DELIM + 
			inputParams + ELEMENT_DELIM + 
			outputParams;
	}

	@Override
	public void processInstruction(ExecutionContext ec)
			throws DMLRuntimeException 
	{
		//do nothing (not applicable because this instruction is only used as
		//meta data container)
	}
}

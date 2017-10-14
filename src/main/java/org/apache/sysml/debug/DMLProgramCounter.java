
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

package org.apache.sysml.debug;

import org.apache.sysml.parser.DMLProgram;


public class DMLProgramCounter {

	private String namespace; //currently executing namespace 
	private String fname; //currently executing  function name
	private int programBlockNumber; //currently executing program block number within current function
	private int instNumber; //currently executing instruction number within current program block
	
	private long instID; //currently executing instruction  
	private int lineNumber; //currently executing line number (not always correctly set)

	/** 
	 * Constructor for DML pc
	 */
	public DMLProgramCounter() {
		instID = 0;
		lineNumber = 0;
	}

	/**
	 * Basic parameterized constructor for DML pc
	 * @param name Current namespace 
	 * @param fn  Current function name in namespace
	 * @param blockNum Current program block within function
	 * @param instNum Current instruction within program block
	 */
	public DMLProgramCounter(String name, String fn, int blockNum, int instNum) {
		this();
		namespace = name;
		fname = fn;		
		programBlockNumber = blockNum;
		instNumber = instNum;
	}

	/**
	 * Getter for namespace field
	 * @return Current pc's namespace
	 */
	public String getNamespace() {
		return namespace;
	}

	/**
	 * Getter for function name field
	 * @return Current pc's function name
	 */
	public String getFunctionName() {
		return fname;
	}
	
	/**
	 * Getter for program block number field
	 * @return Current pc's program block number
	 */
	public int getProgramBlockNumber() {
		return programBlockNumber;
	}

	/**
	 * Getter for instruction number field
	 * @return Current pc's instruction number
	 */
	public int getInstNumber() {
		return instNumber;
	}

	/**
	 * Getter for instruction unique identifier field
	 * @return Current pc's instruction ID
	 */
	public long getInstID() {
		return instID;
	}

	/**
	 * Getter for line number field
	 * @return Current pc's line number
	 */
	public int getLineNumber() {
		return lineNumber;
	}

	/**
	 * Setter for namespace field
	 * @param name Current pc's namespace
	 */
	public void setNamespace(String name) {
		namespace = name;
	}
	/**
	 * Setter for function name field
	 * @param fn Current pc's function name
	 */
	public void setFunctionName(String fn) {
		fname = fn;
	}

	/**
	 * Setter for program block number field
	 * @param blockNum Current pc's program block number 
	 */
	public void setProgramBlockNumber(int blockNum) {
		programBlockNumber = blockNum;
	}

	/**
	 * Setter for instruction number field
	 * @param instNum Current pc's instruction number
	 */
	public void setInstNumber(int instNum) {
		instNumber = instNum;
	}

	/**
	 * Setter for instruction unique identifier field
	 * @param instID Current pc's instruction unique ID
	 */
	public void setInstID(long instID) {
		this.instID = instID;
	}

	/**
	 * Setter for line number field
	 * @param lineNum Current pc's line number
	 */
	public void setLineNumber(int lineNum) {
		lineNumber = lineNum;
	}

	/**
	 * Displays a pretty-printed program counter
	 * @return Current pc
	 */
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(DMLProgram.constructFunctionKey(this.namespace, this.fname));
		sb.append(" instID ");
		sb.append(this.instID);
		sb.append(": (line ");
		sb.append(this.lineNumber);
		sb.append(")");
		return sb.toString();
	}
	
	/**
	 * Displays a pretty-printed program counter without instructionID
	 * @return Current pc
	 */
	public String toStringWithoutInstructionID() {
		StringBuilder sb = new StringBuilder();
		sb.append(DMLProgram.constructFunctionKey(this.namespace, this.fname));
		// sb.append(" instID ");
		// sb.append(this.instID);
		sb.append(": (line ");
		sb.append(this.lineNumber);
		sb.append(")");
		return sb.toString();
	}
}

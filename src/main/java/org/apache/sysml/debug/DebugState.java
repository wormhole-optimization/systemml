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

import java.util.Stack;

import org.apache.sysml.api.DMLScript;
import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.controlprogram.LocalVariableMap;

public class DebugState 
{
	
	public String [] dmlScript;
	public Stack<DMLFrame> callStack = new Stack<>();
	public DMLProgramCounter pc = null, prevPC = null;
	public LocalVariableMap frameVariables=null;
	public String dbCommand=null;
	public String dbCommandArg=null;
	public boolean suspend = false;
	public volatile boolean nextCommand = false;
	
	private static DebugState instance = null;
	
	static {
		instance = new DebugState(); 
	}
	
	protected DebugState() { 
		// So that one cannot instantiate DebugState and violate singleton pattern
	}
	
	public static DebugState getInstance() {
	  return instance;
	}
	
	/////////////////////////////////
	// DML debugger public methods //
	/////////////////////////////////	
	
	/**
	 * Getter for current frame's program counter
	 * @return Current frame program counter
	 */
	public DMLProgramCounter getPC() {
		if(!DMLScript.ENABLE_DEBUG_MODE) {
			System.err.println("Error: This functionality (getPC) is available only in debug mode");
			//// Fatal error to avoid unintentional bugs 
			throw new DMLRuntimeException("Error: This functionality (getPC) is available only in debug mode");
		}
		return pc;
	}

	/**
	 * Getter for current frame's local variables
	 * @return Current frame local variables
	 */
	public LocalVariableMap getVariables() {
		return frameVariables;
	}
	
	/**
	 * Getter for current frame 
	 * @return Current frame
	 */
	public DMLFrame getCurrentFrame() {
		DMLFrame frame = new DMLFrame(frameVariables, pc);
		return frame;
	}
	
	/**
	 * Setter for current frame's local variables
	 * 
	 * @param vars local variables
	 */
	public void setVariables(LocalVariableMap vars) {
		frameVariables = vars;
	}
	
	/**
	 * Is runtime ready to accept next command?
	 * @return  true if the user interface can accept next command
	 */
	public boolean canAcceptNextCommand() {
		return nextCommand;
	}
	
	/**
	 * Set DML script field
	 * @param lines DML script lines of code 
	 */
	public void setDMLScript(String [] lines) {
		dmlScript = lines;
	}
	
	/**
	 * Print DML script source line
	 * @param lineNum DML script line number 
	 */
	public void printDMLSourceLine(int lineNum) {
		if (lineNum > 0 && lineNum < dmlScript.length)
			System.out.format("%-4d %s\n",lineNum, dmlScript[lineNum-1]);
	}
	
	/**
	 * Set debugger command into current runtime 
	 * @param command Debugger command
	 */
	public void setCommand(String command) {
		this.dbCommand = command;
	}

	/**
	 * Set debugger command argument into current runtime 
	 * @param cmdArg Debugger command argument
	 */
	public void setCommandArg(String cmdArg) {
		this.dbCommandArg = cmdArg;
	}
	
	/**
	 * Put current frame into stack due to function call
	 * @param vars Caller's frame symbol table
	 * @param pc Caller's frame program counter
	 */
	public void pushFrame(LocalVariableMap vars, DMLProgramCounter pc) {		
		callStack.push(new DMLFrame(vars, pc));
	}
	
	/**
	 * Pop frame from stack as function call is done 
	 * @return Callee's frame (before function call) 
	 */
	public DMLFrame popFrame() {
		if (callStack.isEmpty())
			return null;
		return callStack.pop();		
	}

	/**
	 * Get current call stack (if any) 
	 * @return Stack callStack 
	 */
	public Stack<DMLFrame> getCallStack() {
		if (callStack.isEmpty())
			return null;
		return callStack;
	}

	/**
	 * Display a full DML stack trace for a runtime exception.
	 * 
	 * @param e the exception
	 */
	public void getDMLStackTrace(Exception e) {		
		System.err.format("Runtime exception raised %s\n", e.toString());
		System.err.println("\t at " + this.pc.toString());		
		if (this.callStack != null) {
			for (int i = callStack.size(); i > 0; i--) {			
				DMLFrame frame = callStack.get(i-1);
				System.err.println("\t at " + frame.getPC().toString());
			}
		}
	}
}

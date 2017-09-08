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

package org.apache.sysml.api.jmlc;

import java.util.HashMap;
import java.util.Set;

import org.apache.sysml.api.DMLException;
import org.apache.sysml.runtime.controlprogram.caching.FrameObject;
import org.apache.sysml.runtime.controlprogram.caching.MatrixObject;
import org.apache.sysml.runtime.instructions.cp.Data;
import org.apache.sysml.runtime.instructions.cp.ScalarObject;
import org.apache.sysml.runtime.matrix.data.FrameBlock;
import org.apache.sysml.runtime.matrix.data.MatrixBlock;
import org.apache.sysml.runtime.util.DataConverter;

/**
 * A ResultVariables object holds the data returned by a call
 * to {@link PreparedScript}'s {@link PreparedScript#executeScript executeScript}
 * method, which executes a DML/PyDML script.
 *
 */
public class ResultVariables 
{
	private HashMap<String, Data> _out = null;
	
	public ResultVariables() {
		_out = new HashMap<String, Data>();
	}
	
	/**
	 * Obtain the output variable names held by this ResultVariables object.
	 * 
	 * @return the set of output variable names
	 */
	public Set<String> getVariableNames() {
		return _out.keySet();
	}
	
	/**
	 * Obtain the number of output data held by this ResultVariables object.
	 * 
	 * @return the number of output variables with data
	 */
	public int size() {
		return _out.size();
	}
	
	/**
	 * Obtain the matrix represented by the given output variable.
	 * 
	 * @param varname output variable name
	 * @return matrix as a two-dimensional double array
	 * @throws DMLException if DMLException occurs
	 */
	public double[][] getMatrix(String varname) throws DMLException {
		return DataConverter.convertToDoubleMatrix(getMatrixBlock(varname));
	}
	
	/**
	 * Obtain the matrix represented by the given output variable.
	 * Calling this method avoids unnecessary output conversions.
	 * 
	 * @param varname output variable name
	 * @return matrix as matrix block
	 * @throws DMLException if DMLException occurs
	 */
	public MatrixBlock getMatrixBlock(String varname) throws DMLException {
		Data dat = _out.get(varname);
		if( dat == null )
			throw new DMLException("Non-existent output variable: "+varname);
		
		//basic checks for data type	
		if( !(dat instanceof MatrixObject) )
			throw new DMLException("Expected matrix result '"+varname+"' not a matrix.");
		
		//convert output matrix to double array	
		MatrixObject mo = (MatrixObject)dat;
		MatrixBlock mb = mo.acquireRead();
		mo.release();
		return mb;
	}
	
	/**
	 * Obtain the frame represented by the given output variable.
	 * 
	 * @param varname output variable name
	 * @return frame as a two-dimensional string array
	 * @throws DMLException if DMLException occurs
	 */
	public String[][] getFrame(String varname) throws DMLException {
		return DataConverter.convertToStringFrame(getFrameBlock(varname));
	}
	
	/**
	 * Obtain the frame represented by the given output variable.
	 * Calling this method avoids unnecessary output conversions.
	 * 
	 * @param varname output variable name
	 * @return frame as a frame block
	 * @throws DMLException if DMLException occurs
	 */
	public FrameBlock getFrameBlock(String varname) 
		throws DMLException
	{
		Data dat = _out.get(varname);
		if( dat == null )
			throw new DMLException("Non-existent output variable: "+varname);
		
		//basic checks for data type	
		if( !(dat instanceof FrameObject) )
			throw new DMLException("Expected frame result '"+varname+"' not a frame.");
		
		//convert output matrix to double array	
		FrameObject fo = (FrameObject)dat;
		FrameBlock fb = fo.acquireRead();
		fo.release();
		return fb;
	}
	
	/**
	 * Obtain the double value represented by the given output variable.
	 * 
	 * @param varname
	 *            output variable name
	 * @return double value
	 * @throws DMLException if DMLException occurs
	 */
	public double getDouble(String varname) throws DMLException {
		return getScalarObject(varname).getDoubleValue();
	}

	/**
	 * Obtain the boolean value represented by the given output variable.
	 * 
	 * @param varname
	 *            output variable name
	 * @return boolean value
	 * @throws DMLException if DMLException occurs
	 */
	public boolean getBoolean(String varname) throws DMLException {
		return getScalarObject(varname).getBooleanValue();
	}

	/**
	 * Obtain the long value represented by the given output variable.
	 * 
	 * @param varname
	 *            output variable name
	 * @return long value
	 * @throws DMLException if DMLException occurs
	 */
	public long getLong(String varname) throws DMLException {
		return getScalarObject(varname).getLongValue();
	}

	/**
	 * Obtain the string value represented by the given output variable.
	 * 
	 * @param varname
	 *            output variable name
	 * @return string value
	 * @throws DMLException if DMLException occurs
	 */
	public String getString(String varname) throws DMLException {
		return getScalarObject(varname).getStringValue();
	}

	/**
	 * Obtain the ScalarObject represented by the given output variable.
	 * 
	 * @param varname
	 *            output variable name
	 * @return ScalarObject
	 * @throws DMLException if DMLException occurs
	 */
	public ScalarObject getScalarObject(String varname) throws DMLException {
		Data dat = _out.get(varname);
		if( dat == null )
			throw new DMLException("Non-existent output variable: " + varname);
		if (!(dat instanceof ScalarObject))
			throw new DMLException("Expected scalar result '" + varname + "' not a scalar.");
		return (ScalarObject) dat;
	}
	
	/**
	 * Add the output variable name and generated output data to the ResultVariable
	 * object. Called during the execution of {@link PreparedScript}'s
	 * {@link PreparedScript#executeScript executeScript} method.
	 * 
	 * @param ovar output variable name
	 * @param data generated output data
	 */
	protected void addResult(String ovar, Data data) {
		_out.put(ovar, data);
	}
}

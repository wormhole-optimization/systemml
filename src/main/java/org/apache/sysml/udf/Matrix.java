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

import java.io.IOException;

import org.apache.sysml.conf.ConfigurationManager;
import org.apache.sysml.hops.OptimizerUtils;
import org.apache.sysml.parser.Expression;
import org.apache.sysml.runtime.controlprogram.caching.MatrixObject;
import org.apache.sysml.runtime.io.MatrixReader;
import org.apache.sysml.runtime.io.MatrixReaderFactory;
import org.apache.sysml.runtime.matrix.MatrixCharacteristics;
import org.apache.sysml.runtime.matrix.MetaDataFormat;
import org.apache.sysml.runtime.matrix.data.InputInfo;
import org.apache.sysml.runtime.matrix.data.MatrixBlock;
import org.apache.sysml.runtime.matrix.data.OutputInfo;
import org.apache.sysml.runtime.util.DataConverter;

/**
 * Class to represent the matrix input type
 * 
 * 
 * 
 */
public class Matrix extends FunctionParameter 
{
	private static final long serialVersionUID = -1058329938431848909L;
	public static final String DEFAULT_FILENAME = "ext_funct";
	
	private String _filePath;
	private long _rows;
	private long _cols;
	private ValueType _vType;
	private MatrixObject _mo;

	public enum ValueType {
		Double,
		Integer
	}
	
	/**
	 * This constructor invokes Matrix(String path, long rows, long cols, ValueType vType)
	 * with a default filename of ExternalFunctionProgramBlockCP and hence, should only
	 * be used by CP external functions.
	 * 
	 * @param rows number of rows
	 * @param cols number of columns
	 * @param vType value type
	 */
	public Matrix(long rows, long cols, ValueType vType) {
		this( DEFAULT_FILENAME, rows, cols, vType );
	}

	/**
	 * Constructor that takes matrix file path, num rows, num cols, and matrix
	 * value type as parameters.
	 * 
	 * @param path file path
	 * @param rows number of rows
	 * @param cols number of columns
	 * @param vType value type
	 */
	public Matrix(String path, long rows, long cols, ValueType vType) {
		super(FunctionParameterType.Matrix);
		_filePath = path;
		_rows = rows;
		_cols = cols;
		_vType = vType;
	}
	
	public Matrix(MatrixObject mo, ValueType vType) {
		super(FunctionParameterType.Matrix);
		_filePath = mo.getFileName();
		_rows = mo.getNumRows();
		_cols = mo.getNumColumns();
		_vType = vType;
		_mo = mo;
	}
	
	public void setMatrixObject( MatrixObject mo ) {
		_mo = mo;
	}
	
	public MatrixObject getMatrixObject() {
		return _mo;
	}

	/**
	 * Method to get file path for matrix.
	 * 
	 * @return file path
	 */
	public String getFilePath() {
		return _filePath;
	}

	/**
	 * Method to get the number of rows in the matrix.
	 * 
	 * @return number of rows
	 */
	public long getNumRows() {
		return _rows;
	}

	/**
	 * Method to get the number of cols in the matrix.
	 * 
	 * @return number of columns
	 */

	public long getNumCols() {
		return _cols;
	}

	/**
	 * Method to get value type for this matrix.
	 * 
	 * @return value type
	 */
	public ValueType getValueType() {
		return _vType;
	}

	/**
	 * Method to get matrix as double array. This should only be used if the
	 * user knows the matrix fits in memory. We are using the dense
	 * representation.
	 * 
	 * @return matrix as two-dimensional double array
	 * @throws IOException if IOException occurs
	 */
	public double[][] getMatrixAsDoubleArray() throws IOException {
		double[][] ret = null;
		
		if( _mo != null ) { //CP ext function
			MatrixBlock mb = _mo.acquireRead();
			ret = DataConverter.convertToDoubleMatrix( mb );
			_mo.release();
		}
		else { //traditional ext function (matrix file produced by reblock)
			MatrixReader reader = MatrixReaderFactory.createMatrixReader(InputInfo.TextCellInputInfo);
			MatrixBlock mb = reader.readMatrixFromHDFS(this.getFilePath(), _rows, _cols, -1, -1, -1);
			ret = DataConverter.convertToDoubleMatrix( mb );
		}
			
		return ret;

	}

	/**
	 * Method to set matrix as double array. This should only be used if the
	 * user knows the matrix fits in memory. We are using the dense
	 * representation.
	 * 
	 * @param data matrix as 2-dimensional double array
	 * @throws IOException if IOException occurs
	 */
	public void setMatrixDoubleArray(double[][] data) throws IOException {
		MatrixBlock mb = DataConverter.convertToMatrixBlock(data);
		setMatrixDoubleArray(mb, OutputInfo.BinaryBlockOutputInfo, InputInfo.BinaryBlockInputInfo);
	}
	
	/**
	 * Method to set matrix as double array. This should only be used if the
	 * user knows the matrix fits in memory. We are using the dense
	 * representation.
	 * 
	 * @param data matrix as double array
	 * @throws IOException if IOException occurs
	 */
	public void setMatrixDoubleArray(double[] data) throws IOException {
		MatrixBlock mb = DataConverter.convertToMatrixBlock(data, true);
		setMatrixDoubleArray(mb, OutputInfo.BinaryBlockOutputInfo, InputInfo.BinaryBlockInputInfo);
	}
	
	/**
	 * Method to set matrix as double array. This should only be used if the
	 * user knows the matrix fits in memory. We are using the dense
	 * representation.
	 * 
	 * @param mb matrix block
	 * @param oinfo output info
	 * @param iinfo input info
	 * @throws IOException if IOException occurs
	 */
	public void setMatrixDoubleArray(MatrixBlock mb, OutputInfo oinfo, InputInfo iinfo) 
		throws IOException 
	{
		_rows = mb.getNumRows();
		_cols = mb.getNumColumns();
		long nnz = mb.getNonZeros();
		int rblen = ConfigurationManager.getBlocksize();
		int cblen = ConfigurationManager.getBlocksize();
		
		MatrixCharacteristics mc = new MatrixCharacteristics(_rows, _cols, rblen, cblen, nnz);
		MetaDataFormat mfmd = new MetaDataFormat(mc, oinfo, iinfo);
		try {
			//check for correct sparse/dense representation
			if( mb.getInMemorySize() < OptimizerUtils.SAFE_REP_CHANGE_THRES )
				mb.examSparsity();
			
			//construct output matrix object
			_mo = new MatrixObject(Expression.ValueType.DOUBLE, _filePath, mfmd);
			_mo.acquireModify( mb );
			_mo.release();
		} 
		catch(Exception e) {
			throw new IOException(e);
		} 
	}
}
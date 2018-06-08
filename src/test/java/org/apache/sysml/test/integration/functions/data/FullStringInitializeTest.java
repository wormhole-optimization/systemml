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

package org.apache.sysml.test.integration.functions.data;

import org.junit.Assert;
import org.junit.Test;
import org.apache.sysml.api.DMLScript.RUNTIME_PLATFORM;
import org.apache.sysml.hops.OptimizerUtils;
import org.apache.sysml.lops.LopProperties.ExecType;
import org.apache.sysml.parser.Expression.ValueType;
import org.apache.sysml.runtime.matrix.data.InputInfo;
import org.apache.sysml.runtime.matrix.data.MatrixBlock;
import org.apache.sysml.runtime.util.DataConverter;
import org.apache.sysml.test.integration.AutomatedTestBase;
import org.apache.sysml.test.integration.TestConfiguration;
import org.apache.sysml.test.utils.TestUtils;

/**
 * 
 * 
 */
public class FullStringInitializeTest extends AutomatedTestBase 
{
	
	private final static String TEST_NAME = "StrInit";
	private final static String TEST_DIR = "functions/data/";
	private final static String TEST_CLASS_DIR = TEST_DIR + FullStringInitializeTest.class.getSimpleName() + "/";
	
	private final static double eps = 1e-10;
	
	private final static int rowsMatrix = 73;
	private final static int colsMatrix = 21;
	private final static double spSparse = 0.1;
	private final static double spDense = 0.9;
	
	private enum InputType {
		COL_VECTOR,
		ROW_VECTOR,
		MATRIX
	}
	
	private enum ErrorType {
		NO_ERROR,
		TOO_FEW,
		TOO_MANY
	}
	
	@Override
	public void setUp() 
	{
		addTestConfiguration(TEST_NAME,
			new TestConfiguration(TEST_CLASS_DIR, TEST_NAME, new String[]{"A"}));
	}

	
	@Test
	public void testStringIntializeColVectorIntDenseNoErrorCP() 
	{
		runStringInitializeTest(InputType.COL_VECTOR, ValueType.INT, false, ErrorType.NO_ERROR, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeRowVectorIntDenseNoErrorCP() 
	{
		runStringInitializeTest(InputType.ROW_VECTOR, ValueType.INT, false, ErrorType.NO_ERROR, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeMatrixIntDenseNoErrorCP() 
	{
		runStringInitializeTest(InputType.MATRIX, ValueType.INT, false, ErrorType.NO_ERROR, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeColVectorDoubleDenseNoErrorCP() 
	{
		runStringInitializeTest(InputType.COL_VECTOR, ValueType.DOUBLE, false, ErrorType.NO_ERROR, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeRowVectorDoubleDenseNoErrorCP() 
	{
		runStringInitializeTest(InputType.ROW_VECTOR, ValueType.DOUBLE, false, ErrorType.NO_ERROR, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeMatrixDoubleDenseNoErrorCP() 
	{
		runStringInitializeTest(InputType.MATRIX, ValueType.DOUBLE, false, ErrorType.NO_ERROR, ExecType.CP);
	}

	@Test
	public void testStringIntializeColVectorIntSparseNoErrorCP() 
	{
		runStringInitializeTest(InputType.COL_VECTOR, ValueType.INT, true, ErrorType.NO_ERROR, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeRowVectorIntSparseNoErrorCP() 
	{
		runStringInitializeTest(InputType.ROW_VECTOR, ValueType.INT, true, ErrorType.NO_ERROR, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeMatrixIntSparseNoErrorCP() 
	{
		runStringInitializeTest(InputType.MATRIX, ValueType.INT, true, ErrorType.NO_ERROR, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeColVectorDoubleSparseNoErrorCP() 
	{
		runStringInitializeTest(InputType.COL_VECTOR, ValueType.DOUBLE, true, ErrorType.NO_ERROR, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeRowVectorDoubleSparseNoErrorCP() 
	{
		runStringInitializeTest(InputType.ROW_VECTOR, ValueType.DOUBLE, true, ErrorType.NO_ERROR, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeMatrixDoubleSparseNoErrorCP() 
	{
		runStringInitializeTest(InputType.MATRIX, ValueType.DOUBLE, true, ErrorType.NO_ERROR, ExecType.CP);
	}

	@Test
	public void testStringIntializeColVectorIntDenseTooFewCP() 
	{
		runStringInitializeTest(InputType.COL_VECTOR, ValueType.INT, false, ErrorType.TOO_FEW, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeRowVectorIntDenseTooFewCP() 
	{
		runStringInitializeTest(InputType.ROW_VECTOR, ValueType.INT, false, ErrorType.TOO_FEW, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeMatrixIntDenseTooFewCP() 
	{
		runStringInitializeTest(InputType.MATRIX, ValueType.INT, false, ErrorType.TOO_FEW, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeColVectorDoubleDenseTooFewCP() 
	{
		runStringInitializeTest(InputType.COL_VECTOR, ValueType.DOUBLE, false, ErrorType.TOO_FEW, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeRowVectorDoubleDenseTooFewCP() 
	{
		runStringInitializeTest(InputType.ROW_VECTOR, ValueType.DOUBLE, false, ErrorType.TOO_FEW, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeMatrixDoubleDenseTooFewCP() 
	{
		runStringInitializeTest(InputType.MATRIX, ValueType.DOUBLE, false, ErrorType.TOO_FEW, ExecType.CP);
	}

	@Test
	public void testStringIntializeColVectorIntSparseTooFewCP() 
	{
		runStringInitializeTest(InputType.COL_VECTOR, ValueType.INT, true, ErrorType.TOO_FEW, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeRowVectorIntSparseTooFewCP() 
	{
		runStringInitializeTest(InputType.ROW_VECTOR, ValueType.INT, true, ErrorType.TOO_FEW, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeMatrixIntSparseTooFewCP() 
	{
		runStringInitializeTest(InputType.MATRIX, ValueType.INT, true, ErrorType.TOO_FEW, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeColVectorDoubleSparseTooFewCP() 
	{
		runStringInitializeTest(InputType.COL_VECTOR, ValueType.DOUBLE, true, ErrorType.TOO_FEW, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeRowVectorDoubleSparseTooFewCP() 
	{
		runStringInitializeTest(InputType.ROW_VECTOR, ValueType.DOUBLE, true, ErrorType.TOO_FEW, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeMatrixDoubleSparseTooFewCP() 
	{
		runStringInitializeTest(InputType.MATRIX, ValueType.DOUBLE, true, ErrorType.TOO_FEW, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeColVectorIntDenseTooManyCP() 
	{
		runStringInitializeTest(InputType.COL_VECTOR, ValueType.INT, false, ErrorType.TOO_MANY, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeRowVectorIntDenseTooManyCP() 
	{
		runStringInitializeTest(InputType.ROW_VECTOR, ValueType.INT, false, ErrorType.TOO_MANY, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeMatrixIntDenseTooManyCP() 
	{
		runStringInitializeTest(InputType.MATRIX, ValueType.INT, false, ErrorType.TOO_MANY, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeColVectorDoubleDenseTooManyCP() 
	{
		runStringInitializeTest(InputType.COL_VECTOR, ValueType.DOUBLE, false, ErrorType.TOO_MANY, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeRowVectorDoubleDenseTooManyCP() 
	{
		runStringInitializeTest(InputType.ROW_VECTOR, ValueType.DOUBLE, false, ErrorType.TOO_MANY, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeMatrixDoubleDenseManyFewCP() 
	{
		runStringInitializeTest(InputType.MATRIX, ValueType.DOUBLE, false, ErrorType.TOO_MANY, ExecType.CP);
	}

	@Test
	public void testStringIntializeColVectorIntSparseTooManyCP() 
	{
		runStringInitializeTest(InputType.COL_VECTOR, ValueType.INT, true, ErrorType.TOO_MANY, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeRowVectorIntSparseTooManyCP() 
	{
		runStringInitializeTest(InputType.ROW_VECTOR, ValueType.INT, true, ErrorType.TOO_MANY, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeMatrixIntSparseTooManyCP() 
	{
		runStringInitializeTest(InputType.MATRIX, ValueType.INT, true, ErrorType.TOO_MANY, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeColVectorDoubleSparseTooManyCP() 
	{
		runStringInitializeTest(InputType.COL_VECTOR, ValueType.DOUBLE, true, ErrorType.TOO_MANY, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeRowVectorDoubleSparseTooManyCP() 
	{
		runStringInitializeTest(InputType.ROW_VECTOR, ValueType.DOUBLE, true, ErrorType.TOO_MANY, ExecType.CP);
	}
	
	@Test
	public void testStringIntializeMatrixDoubleSparseTooManyCP() 
	{
		runStringInitializeTest(InputType.MATRIX, ValueType.DOUBLE, true, ErrorType.TOO_MANY, ExecType.CP);
	}

	//few additional tests for MR to test that string initialize is always forced into CP
	
	@Test
	public void testStringIntializeColVectorIntDenseNoErrorMR() 
	{
		runStringInitializeTest(InputType.COL_VECTOR, ValueType.INT, false, ErrorType.NO_ERROR, ExecType.MR);
	}
	
	@Test
	public void testStringIntializeRowVectorIntDenseNoErrorMR() 
	{
		runStringInitializeTest(InputType.ROW_VECTOR, ValueType.INT, false, ErrorType.NO_ERROR, ExecType.MR);
	}

	@Test
	public void testStringIntializeMatrixIntDenseNoErrorMR() 
	{
		runStringInitializeTest(InputType.MATRIX, ValueType.INT, false, ErrorType.NO_ERROR, ExecType.MR);
	}
	
	
	/**
	 * 
	 * @param sparseM1
	 * @param sparseM2
	 * @param instType
	 */
	private void runStringInitializeTest( InputType intype, ValueType vt, boolean sparse, ErrorType errtype, ExecType instType)
	{
		//rtplatform for MR
		RUNTIME_PLATFORM platformOld = rtplatform;
		rtplatform = (instType==ExecType.MR) ? RUNTIME_PLATFORM.HADOOP : RUNTIME_PLATFORM.HYBRID;
		
		try
		{
			int cols = (intype==InputType.COL_VECTOR) ? 1 : colsMatrix;
			int rows = (intype==InputType.ROW_VECTOR) ? 1 : rowsMatrix;
			double sparsity = (sparse) ? spSparse : spDense;
			long nnz = (long)Math.round(sparsity * rows * cols);
			
			//generate data
			double[][] A = getRandomMatrix(rows, cols, -5, 5, sparsity, 7); 
			if( vt == ValueType.INT )
				A = TestUtils.round(A);
			StringBuilder sb = new StringBuilder();
			for( int i=0; i<rows; i++ )
				for( int j=0; j<cols; j++ )
				{
					if( errtype==ErrorType.TOO_FEW && i==j )
						continue;
					if( sb.length()>0 )
						sb.append(" ");
					sb.append(A[i][j]);
				}
			if( errtype==ErrorType.TOO_MANY ){
				sb.append(" ");
				sb.append("7");
			}
			
			TestConfiguration config = getTestConfiguration(TEST_NAME);
			loadTestConfiguration(config);
			
			// This is for running the junit test the new way, i.e., construct the arguments directly
			String HOME = SCRIPT_DIR + TEST_DIR;
			fullDMLScriptName = HOME + TEST_NAME + ".dml";
			programArgs = new String[]{"-args",
				sb.toString(), String.valueOf(rows), String.valueOf(cols), output("A") };
			
			fullRScriptName = HOME + TEST_NAME + ".R";
	
			//run the testcase
			boolean expectExcept = (errtype!=ErrorType.NO_ERROR);
			runTest(true, expectExcept, null, -1); 
	
			if( !expectExcept ) {
				//compare matrices 
				MatrixBlock ret = DataConverter.readMatrixFromHDFS(output("A"), InputInfo.TextCellInputInfo,
					rows, cols, OptimizerUtils.DEFAULT_BLOCKSIZE, OptimizerUtils.DEFAULT_BLOCKSIZE, nnz, null);
				double[][] dret = DataConverter.convertToDoubleMatrix(ret);
				TestUtils.compareMatrices(A, dret, rows, cols, eps);
			}
		}
		catch(Exception ex)
		{
			ex.printStackTrace();
			Assert.fail(ex.getMessage());
		}
		finally
		{
			rtplatform = platformOld;
		}
	}	
}
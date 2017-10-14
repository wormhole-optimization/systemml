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

package org.apache.sysml.test.integration.functions.external;

import java.util.HashMap;

import org.junit.Test;

import org.apache.sysml.runtime.matrix.data.MatrixValue.CellIndex;
import org.apache.sysml.test.integration.AutomatedTestBase;
import org.apache.sysml.test.integration.TestConfiguration;
import org.apache.sysml.test.utils.TestUtils;

public class DynProjectTest extends AutomatedTestBase 
{
	
	private final static String TEST_NAME = "DynProject";
	private final static String TEST_DIR = "functions/external/";
	private final static String TEST_CLASS_DIR = TEST_DIR + DynProjectTest.class.getSimpleName() + "/";
	private final static double eps = 1e-10;
	
	private final static int rows = 1154;
	private final static int size = 104;
	
	private final static double sparsity1 = 0.7;
	private final static double sparsity2 = 0.3;
	
	
	@Override
	public void setUp() 
	{
		addTestConfiguration(TEST_NAME,
			new TestConfiguration(TEST_CLASS_DIR, TEST_NAME, new String[] { "Rout" }) );
	}

	
	@Test
	public void testProjectMatrixDense() 
	{
		runDynProjectTest(false, false);
	}
	
	@Test
	public void testProjectMatrixSparse() 
	{
		runDynProjectTest(false, true);
	}
	
	@Test
	public void testProjectVectorDense() 
	{
		runDynProjectTest(true, false);
	}
	
	@Test
	public void testProjectVectorSparse() 
	{
		runDynProjectTest(true, true);
	}

		
	/**
	 * 
	 * @param vector
	 * @param sparse
	 */
	private void runDynProjectTest( boolean vector, boolean sparse )
	{		
		double sparsity = sparse ? sparsity2 : sparsity1;
		int cols = vector ? 1 : rows;
		
		TestConfiguration config = getTestConfiguration(TEST_NAME);
		config.addVariable("rows", rows);
		loadTestConfiguration(config);
		
		/* This is for running the junit test the new way, i.e., construct the arguments directly */
		String HOME = SCRIPT_DIR + TEST_DIR;
		fullDMLScriptName = HOME + TEST_NAME + ".dml";
		programArgs = new String[]{"-args", input("X"), input("c"),
			Integer.toString(rows), Integer.toString(cols), Integer.toString(size), output("Y") };
		
		rCmd = getRCmd(inputDir(), expectedDir());
		
		long seed = System.nanoTime();
		double[][] X = getRandomMatrix(rows, cols, 0, 1, sparsity, seed);
		double[][] c = TestUtils.round(getRandomMatrix(1, size, 1-0.49, rows+0.49, 1, seed));
		
		writeInputMatrix("X", X, true);
		writeInputMatrix("c", c, true);
		
		runTest(true, false, null, -1);
		runRScript(true);
		
		//compare matrices
		HashMap<CellIndex, Double> dmlfile = readDMLMatrixFromHDFS("Y");
		HashMap<CellIndex, Double> rfile  = readRMatrixFromFS("Y.mtx");
		TestUtils.compareMatrices(dmlfile, rfile, eps, "DML", "R");
	}
}
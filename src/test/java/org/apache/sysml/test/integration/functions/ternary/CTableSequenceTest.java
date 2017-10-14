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

package org.apache.sysml.test.integration.functions.ternary;

import java.util.HashMap;

import org.junit.Test;

import org.apache.sysml.api.DMLScript;
import org.apache.sysml.api.DMLScript.RUNTIME_PLATFORM;
import org.apache.sysml.hops.TernaryOp;
import org.apache.sysml.lops.LopProperties.ExecType;
import org.apache.sysml.runtime.matrix.data.MatrixValue.CellIndex;
import org.apache.sysml.test.integration.AutomatedTestBase;
import org.apache.sysml.test.integration.TestConfiguration;
import org.apache.sysml.test.utils.TestUtils;

/**
 * This test investigates the specific Hop-Lop rewrite ctable(seq(1,nrow(X)),X).
 * 
 * NOTES: 
 * * table in R treats every distinct value of X as a specific value, while
 *   we cast those double values to long. Hence, we need to round the generated 
 *   dataset.
 * * May, 16 2014: extended tests to include aggregate because some specific issues
 *   only show up on subsequent GMR operations after ctable produced the output in
 *   matrix cell.
 * 
 */
public class CTableSequenceTest extends AutomatedTestBase 
{
	
	private final static String TEST_NAME1 = "CTableSequenceLeft";
	private final static String TEST_NAME2 = "CTableSequenceRight";
	
	private final static String TEST_DIR = "functions/ternary/";
	private final static String TEST_CLASS_DIR = TEST_DIR + CTableSequenceTest.class.getSimpleName() + "/";
	private final static double eps = 1e-10;
	
	private final static int rows = 2407;
	private final static int maxVal = 7; 
	
	
	@Override
	public void setUp() 
	{
		TestUtils.clearAssertionInformation();
		addTestConfiguration(TEST_NAME1, new TestConfiguration(TEST_CLASS_DIR, TEST_NAME1, new String[] { "B" }) );
		addTestConfiguration(TEST_NAME2, new TestConfiguration(TEST_CLASS_DIR, TEST_NAME2, new String[] { "B" }) );
	}
	
	@Test
	public void testCTableSequenceLeftNoRewriteSP() 
	{
		runCTableSequenceTest(false, true, false, ExecType.SPARK);
	}
	
	@Test
	public void testCTableSequenceLeftRewriteSP() 
	{
		runCTableSequenceTest(true, true, false, ExecType.SPARK);
	}
	
	@Test
	public void testCTableSequenceRightNoRewriteSP() 
	{
		runCTableSequenceTest(false, false, false, ExecType.SPARK);
	}
	
	@Test
	public void testCTableSequenceRightRewriteSP() 
	{
		runCTableSequenceTest(true, false, false, ExecType.SPARK);
	}
	
	@Test
	public void testCTableSequenceLeftNoRewriteAggSP() 
	{
		runCTableSequenceTest(false, true, true, ExecType.SPARK);
	}
	
	@Test
	public void testCTableSequenceLeftRewriteAggSP() 
	{
		runCTableSequenceTest(true, true, true, ExecType.SPARK);
	}
	
	@Test
	public void testCTableSequenceRightNoRewriteAggSP() 
	{
		runCTableSequenceTest(false, false, true, ExecType.SPARK);
	}
	
	@Test
	public void testCTableSequenceRightRewriteAggSP() 
	{
		runCTableSequenceTest(true, false, true, ExecType.SPARK);
	}

	
	@Test
	public void testCTableSequenceLeftNoRewriteCP() 
	{
		runCTableSequenceTest(false, true, false, ExecType.CP);
	}
	
	@Test
	public void testCTableSequenceLeftRewriteCP() 
	{
		runCTableSequenceTest(true, true, false, ExecType.CP);
	}
	
	@Test
	public void testCTableSequenceLeftNoRewriteMR() 
	{
		runCTableSequenceTest(false, true, false, ExecType.MR);
	}
	
	@Test
	public void testCTableSequenceLeftRewriteMR() 
	{
		runCTableSequenceTest(true, true, false, ExecType.MR);
	}
	
	@Test
	public void testCTableSequenceRightNoRewriteCP() 
	{
		runCTableSequenceTest(false, false, false, ExecType.CP);
	}
	
	@Test
	public void testCTableSequenceRightRewriteCP() 
	{
		runCTableSequenceTest(true, false, false, ExecType.CP);
	}
	
	@Test
	public void testCTableSequenceRightNoRewriteMR() 
	{
		runCTableSequenceTest(false, false, false, ExecType.MR);
	}
	
	@Test
	public void testCTableSequenceRightRewriteMR() 
	{
		runCTableSequenceTest(true, false, false, ExecType.MR);
	}
	
	
	@Test
	public void testCTableSequenceLeftNoRewriteAggCP() 
	{
		runCTableSequenceTest(false, true, true, ExecType.CP);
	}
	
	@Test
	public void testCTableSequenceLeftRewriteAggCP() 
	{
		runCTableSequenceTest(true, true, true, ExecType.CP);
	}
	
	@Test
	public void testCTableSequenceLeftNoRewriteAggMR() 
	{
		runCTableSequenceTest(false, true, true, ExecType.MR);
	}
	
	@Test
	public void testCTableSequenceLeftRewriteAggMR() 
	{
		runCTableSequenceTest(true, true, true, ExecType.MR);
	}
	
	@Test
	public void testCTableSequenceRightNoRewriteAggCP() 
	{
		runCTableSequenceTest(false, false, true, ExecType.CP);
	}
	
	@Test
	public void testCTableSequenceRightRewriteAggCP() 
	{
		runCTableSequenceTest(true, false, true, ExecType.CP);
	}
	
	@Test
	public void testCTableSequenceRightNoRewriteAggMR() 
	{
		runCTableSequenceTest(false, false, true, ExecType.MR);
	}
	
	@Test
	public void testCTableSequenceRightRewriteAggMR() 
	{
		runCTableSequenceTest(true, false, true, ExecType.MR);
	}
	

	/**
	 * 
	 * @param sparseM1
	 * @param sparseM2
	 * @param instType
	 */
	private void runCTableSequenceTest( boolean rewrite, boolean left, boolean withAgg, ExecType et)
	{
		String TEST_NAME = left ? TEST_NAME1 : TEST_NAME2;
		
		//rtplatform for MR
		RUNTIME_PLATFORM platformOld = rtplatform;
		boolean rewriteOld = TernaryOp.ALLOW_CTABLE_SEQUENCE_REWRITES;
		
		switch( et ){
			case MR: rtplatform = RUNTIME_PLATFORM.HADOOP; break;
			case SPARK: rtplatform = RUNTIME_PLATFORM.SPARK; break;
			default: rtplatform = RUNTIME_PLATFORM.HYBRID; break;
		}
	
		boolean sparkConfigOld = DMLScript.USE_LOCAL_SPARK_CONFIG;
		if( rtplatform == RUNTIME_PLATFORM.SPARK )
			DMLScript.USE_LOCAL_SPARK_CONFIG = true;
		
		TernaryOp.ALLOW_CTABLE_SEQUENCE_REWRITES = rewrite;
		
		try
		{
			TestConfiguration config = getTestConfiguration(TEST_NAME);
			loadTestConfiguration(config);
			
			/* This is for running the junit test the new way, i.e., construct the arguments directly */
			String HOME = SCRIPT_DIR + TEST_DIR;
			fullDMLScriptName = HOME + TEST_NAME + ".dml";
			programArgs = new String[]{"-explain","-args", input("A"),
				Integer.toString(rows),
				Integer.toString(1),
				Integer.toString(withAgg?1:0),
				output("B")};
			
			fullRScriptName = HOME + TEST_NAME + ".R";
			rCmd = "Rscript" + " " + fullRScriptName + " " + inputDir() + " " + expectedDir();
			
			//generate actual dataset (always dense because values <=0 invalid)
			double[][] A = TestUtils.floor(getRandomMatrix(rows, 1, 1, maxVal, 1.0, 7)); 
			writeInputMatrix("A", A, true);
	
			runTest(true, false, null, -1); 
			runRScript(true); 
			
			//compare matrices 
			HashMap<CellIndex, Double> dmlfile = readDMLMatrixFromHDFS("B");
			HashMap<CellIndex, Double> rfile  = readRMatrixFromFS("B");
			TestUtils.compareMatrices(dmlfile, rfile, eps, "Stat-DML", "Stat-R");
			
			//w/ rewrite: 4 instead of 6 because seq and aggregation are not required for ctable_expand
			//2 for CP due to reblock jobs for input and table
			if(et != ExecType.SPARK) {
				int expectedNumCompiled = ((et==ExecType.CP) ? 2 :(rewrite ? 4 : 6))+(withAgg ? 1 : 0);
				checkNumCompiledMRJobs(expectedNumCompiled);
			}
		}
		finally {
			rtplatform = platformOld;
			DMLScript.USE_LOCAL_SPARK_CONFIG = sparkConfigOld;
			TernaryOp.ALLOW_CTABLE_SEQUENCE_REWRITES = rewriteOld;
		}
	}
}
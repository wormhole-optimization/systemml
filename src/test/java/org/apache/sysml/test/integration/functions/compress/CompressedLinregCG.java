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

package org.apache.sysml.test.integration.functions.compress;

import java.io.File;
import java.util.HashMap;

import org.apache.sysml.api.DMLScript;
import org.apache.sysml.api.DMLScript.RUNTIME_PLATFORM;
import org.apache.sysml.lops.LopProperties.ExecType;
import org.apache.sysml.runtime.compress.CompressedMatrixBlock;
import org.apache.sysml.runtime.controlprogram.parfor.stat.InfrastructureAnalyzer;
import org.apache.sysml.runtime.matrix.data.MatrixValue.CellIndex;
import org.apache.sysml.test.integration.AutomatedTestBase;
import org.apache.sysml.test.integration.TestConfiguration;
import org.apache.sysml.test.utils.TestUtils;
import org.junit.Assert;
import org.junit.Test;

/**
 * 
 */
public class CompressedLinregCG extends AutomatedTestBase 
{
	private final static String TEST_NAME1 = "LinregCG";
	private final static String TEST_DIR = "functions/compress/";
	private final static String TEST_CONF = "SystemML-config-compress.xml";
	private final static File   TEST_CONF_FILE = new File(SCRIPT_DIR + TEST_DIR, TEST_CONF);
	
	private final static double eps = 1e-4;
	
	private final static int rows = 1468;
	private final static int cols = 980;
		
	private final static double sparsity1 = 0.7; //dense
	private final static double sparsity2 = 0.1; //sparse
	
	private final static int intercept = 0;
	private final static double epsilon = 0.000000001;
	private final static double maxiter = 10;
	private final static double regular = 0.001;
	
	@Override
	public void setUp() {
		TestUtils.clearAssertionInformation();
		addTestConfiguration(TEST_NAME1, new TestConfiguration(TEST_DIR, TEST_NAME1, new String[] { "w" })); 
	}

	@Test
	public void testLinregCGDenseCP() {
		runLinregCGTest(TEST_NAME1, false, ExecType.CP);
	}
	
	@Test
	public void testLinregCGSparseCP() {
		runLinregCGTest(TEST_NAME1, true, ExecType.CP);
	}
	
	@Test
	public void testLinregCGDenseSP() {
		runLinregCGTest(TEST_NAME1, false, ExecType.SPARK);
	}
	
	@Test
	public void testLinregCGSparseSP() {
		runLinregCGTest(TEST_NAME1, true, ExecType.SPARK);
	}
	
	private void runLinregCGTest( String testname,boolean sparse, ExecType instType)
	{
		//rtplatform for MR
		RUNTIME_PLATFORM platformOld = rtplatform;
		switch( instType ){
			case MR: rtplatform = RUNTIME_PLATFORM.HADOOP; break;
			case SPARK: rtplatform = RUNTIME_PLATFORM.HYBRID_SPARK; break;
			default: rtplatform = RUNTIME_PLATFORM.HYBRID; break;
		}
	
		boolean sparkConfigOld = DMLScript.USE_LOCAL_SPARK_CONFIG;
		if( rtplatform == RUNTIME_PLATFORM.HYBRID_SPARK )
			DMLScript.USE_LOCAL_SPARK_CONFIG = true;
		long memOld = InfrastructureAnalyzer.getLocalMaxMemory();
		
		try
		{
			TestConfiguration config = getTestConfiguration(testname);
			loadTestConfiguration(config);
			
			/* This is for running the junit test the new way, i.e., construct the arguments directly */
			String HOME1 = SCRIPT_DIR + "functions/compress/";
			String HOME2 = SCRIPT_DIR + "functions/codegen/";
			fullDMLScriptName = "scripts/algorithms/LinearRegCG.dml";
			programArgs = new String[]{ "-explain", "-stats", "-nvargs", "X="+input("X"), "Y="+input("y"),
					"icpt="+String.valueOf(intercept), "tol="+String.valueOf(epsilon),
					"maxi="+String.valueOf(maxiter), "reg="+String.valueOf(regular), "B="+output("w")};

			fullRScriptName = HOME2 + "Algorithm_LinregCG.R";
			rCmd = "Rscript" + " " + fullRScriptName + " " + 
					HOME1 + INPUT_DIR + " " +
					String.valueOf(intercept) + " " + String.valueOf(epsilon) + " " + 
					String.valueOf(maxiter) + " " + String.valueOf(regular) + " "+ HOME1 + EXPECTED_DIR;
			
			//generate actual datasets
			double[][] X = getRandomMatrix(rows, cols, 1, 1, sparse?sparsity2:sparsity1, 7);
			writeInputMatrixWithMTD("X", X, true);
			double[][] y = getRandomMatrix(rows, 1, 0, 10, 1.0, 3);
			writeInputMatrixWithMTD("y", y, true);
			
			if( rtplatform == RUNTIME_PLATFORM.HYBRID_SPARK  )
				InfrastructureAnalyzer.setLocalMaxMemory(8*1024*1024);
			
			runTest(true, false, null, -1); 
			runRScript(true); 
			
			//compare matrices 
			HashMap<CellIndex, Double> dmlfile = readDMLMatrixFromHDFS("w");
			HashMap<CellIndex, Double> rfile  = readRMatrixFromFS("w");
			TestUtils.compareMatrices(dmlfile, rfile, eps, "Stat-DML", "Stat-R");
			
			Assert.assertTrue(heavyHittersContainsSubString("compress")
				|| heavyHittersContainsSubString("sp_compress"));
		}
		finally {
			rtplatform = platformOld;
			DMLScript.USE_LOCAL_SPARK_CONFIG = sparkConfigOld;
			InfrastructureAnalyzer.setLocalMaxMemory(memOld);
			CompressedMatrixBlock.ALLOW_DDC_ENCODING = true;
		}
	}

	/**
	 * Override default configuration with custom test configuration to ensure
	 * scratch space and local temporary directory locations are also updated.
	 */
	@Override
	protected File getConfigTemplateFile() {
		// Instrumentation in this test's output log to show custom configuration file used for template.
		System.out.println("This test case overrides default configuration with " + TEST_CONF_FILE.getPath());
		return TEST_CONF_FILE;
	}
}

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

package org.apache.sysml.test.integration.functions.codegen;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;

import org.apache.sysml.api.DMLScript;
import org.apache.sysml.api.DMLScript.RUNTIME_PLATFORM;
import org.apache.sysml.hops.OptimizerUtils;
import org.apache.sysml.lops.LopProperties.ExecType;
import org.apache.sysml.runtime.matrix.data.MatrixValue.CellIndex;
import org.apache.sysml.test.integration.AutomatedTestBase;
import org.apache.sysml.test.integration.TestConfiguration;
import org.apache.sysml.test.utils.TestUtils;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

@RunWith(Parameterized.class)
public class RowAggTmplTest extends AutomatedTestBase 
{
	private static final String TEST_NAME = "rowAggPattern";
//	TEST_NAME+"1";  //t(X)%*%(X%*%(lamda*v))
//	TEST_NAME+"2";  //t(X)%*%(lamda*(X%*%v))
//	TEST_NAME+"3";  //t(X)%*%(z+(2-(w*(X%*%v))))
//	TEST_NAME+"4";  //colSums(X/rowSums(X))
//	TEST_NAME+"5";  //t(X)%*%((P*(1-P))*(X%*%v));
//	TEST_NAME+"6";  //t(X)%*%((P[,1]*(1-P[,1]))*(X%*%v));
//	TEST_NAME+"7";  //t(X)%*%(X%*%v-y); sum((X%*%v-y)^2);
//	TEST_NAME+"8";  //colSums((X/rowSums(X))>0.7)
//	TEST_NAME+"9";  //t(X) %*% (v - abs(y))
//	TEST_NAME+"10"; //Y=(X<=rowMins(X)); R=colSums((Y/rowSums(Y)));
//	TEST_NAME+"11"; //y - X %*% v
//	TEST_NAME+"12"; //Y=(X>=v); R=Y/rowSums(Y)
//	TEST_NAME+"13"; //rowSums(X)+rowSums(Y)
//	TEST_NAME+"14"; //colSums(max(floor(round(abs(min(sign(X+Y),1)))),7))
//	TEST_NAME+"15"; //systemml nn - softmax backward
//	TEST_NAME+"16"; //Y=X-rowIndexMax(X); R=Y/rowSums(Y)
//	TEST_NAME+"17"; //MLogreg - vector-matrix w/ indexing
//	TEST_NAME+"18"; //MLogreg - matrix-vector cbind 0s
//	TEST_NAME+"19"; //MLogreg - rowwise dag
//	TEST_NAME+"20"; //1 / (1 - (A / rowSums(A)))
//	TEST_NAME+"21"; //sum(X/rowSums(X))
	private static final int NUM_TESTS = 21;
	
	private static final String TEST_DIR = "functions/codegen/";
	private static final String TEST_CLASS_DIR = TEST_DIR + RowAggTmplTest.class.getSimpleName() + "/";
	private final static String TEST_CONF = "SystemML-config-codegen.xml";
	private final static File   TEST_CONF_FILE = new File(SCRIPT_DIR + TEST_DIR, TEST_CONF);

	private static final double eps = Math.pow(10, -10);

	@Parameterized.Parameters(name = "{index}: testCodegen({0}, rewrites={1}, {2})")
	public static Collection<Object[]> testParams() {
		List<Object[]> params = new ArrayList<>(NUM_TESTS*3);
		for (int testNum = 1; testNum <= NUM_TESTS; testNum++) {
			final String testName = TEST_NAME+testNum;
			params.add(new Object[] {testName, false, ExecType.CP});
			params.add(new Object[] {testName, false, ExecType.SPARK});
			params.add(new Object[] {testName, true, ExecType.CP});
		}
		return params;
	}

	// instantiated with test params
	public RowAggTmplTest(String testName, boolean rewrites, ExecType execType) {
		this.testName = testName;
		this.rewrites = rewrites;
		this.execType = execType;
	}

	private final String testName;
	private final boolean rewrites;
	private final ExecType execType;

	
	@Override
	public void setUp() {
		TestUtils.clearAssertionInformation();
		for(int i=1; i<=21; i++)
			addTestConfiguration( TEST_NAME+i, new TestConfiguration(TEST_CLASS_DIR, TEST_NAME+i, new String[] { String.valueOf(i) }) );
	}

	@Test
	public void testCodegenRowAgg() { testCodegenIntegration(testName, rewrites, execType); }
	
	private void testCodegenIntegration( String testname, boolean rewrites, ExecType instType )
	{	
		boolean oldFlag = OptimizerUtils.ALLOW_ALGEBRAIC_SIMPLIFICATION;
		RUNTIME_PLATFORM platformOld = rtplatform;
		switch( instType ) {
			case MR: rtplatform = RUNTIME_PLATFORM.HADOOP; break;
			case SPARK: rtplatform = RUNTIME_PLATFORM.SPARK; break;
			default: rtplatform = RUNTIME_PLATFORM.HYBRID_SPARK; break;
		}

		final boolean sparkConfigOld = DMLScript.USE_LOCAL_SPARK_CONFIG;
		if( rtplatform == RUNTIME_PLATFORM.SPARK || rtplatform == RUNTIME_PLATFORM.HYBRID_SPARK )
			DMLScript.USE_LOCAL_SPARK_CONFIG = true;

		try
		{
			TestConfiguration config = getTestConfiguration(testname);
			loadTestConfiguration(config);
			
			final String HOME = SCRIPT_DIR + TEST_DIR;
			fullDMLScriptName = HOME + testname + ".dml";
			programArgs = new String[]{"-explain", "recompile_hops", "-stats", "-args", output("S") };
			
			fullRScriptName = HOME + testname + ".R";
			rCmd = getRCmd(inputDir(), expectedDir());			

			OptimizerUtils.ALLOW_ALGEBRAIC_SIMPLIFICATION = rewrites;

			runTest(true, false, null, -1); 
			runRScript(true); 
			
			//compare matrices 
			HashMap<CellIndex, Double> dmlfile = readDMLMatrixFromHDFS("S");
			HashMap<CellIndex, Double> rfile  = readRMatrixFromFS("S");
			TestUtils.compareMatrices(dmlfile, rfile, eps, "Stat-DML", "Stat-R");
			Assert.assertTrue(heavyHittersContainsSubString("spoofRA") 
					|| heavyHittersContainsSubString("sp_spoofRA"));
			
			//ensure full aggregates for certain patterns
			if( testname.equals(TEST_NAME+15) )
				Assert.assertTrue(!heavyHittersContainsSubString("uark+"));
			if( testname.equals(TEST_NAME+17) )
				Assert.assertTrue(!heavyHittersContainsSubString("rangeReIndex"));
		}
		finally {
			rtplatform = platformOld;
			DMLScript.USE_LOCAL_SPARK_CONFIG = sparkConfigOld;
			OptimizerUtils.ALLOW_ALGEBRAIC_SIMPLIFICATION = oldFlag;
			OptimizerUtils.ALLOW_AUTO_VECTORIZATION = true;
			OptimizerUtils.ALLOW_OPERATOR_FUSION = true;
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

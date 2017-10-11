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

package org.apache.sysml.test.integration.functions.unary.matrix;

import org.junit.Test;
import org.apache.sysml.api.DMLScript;
import org.apache.sysml.api.DMLScript.RUNTIME_PLATFORM;
import org.apache.sysml.test.integration.AutomatedTestBase;
import org.apache.sysml.test.integration.TestConfiguration;
import org.apache.sysml.test.utils.TestUtils;

public class RoundTest extends AutomatedTestBase 
{
	private enum TEST_TYPE { 
		ROUND ("RoundTest"), 
		FLOOR ("Floor"),
		CEIL ("Ceil"),
		CEILING ("Ceiling");
					
		String scriptName = null;
		TEST_TYPE(String name) {
			this.scriptName = name;
		}
	}
	
	private final static String TEST_DIR = "functions/unary/matrix/";
	private static final String TEST_CLASS_DIR = TEST_DIR + RoundTest.class.getSimpleName() + "/";
	
	private final static int rows1 = 200;
	private final static int cols1 = 200;    
	private final static int rows2 = 1500;
	private final static int cols2 = 10;    
	private final static double sparsity1 = 0.1;
	private final static double sparsity2 = 0.8;
	private final static double sparsity3 = 1.0;
	
	@Override
	public void setUp() {
		addTestConfiguration(TEST_TYPE.ROUND.scriptName, new TestConfiguration(TEST_CLASS_DIR, TEST_TYPE.ROUND.scriptName, new String[] { "R" }));
		addTestConfiguration(TEST_TYPE.FLOOR.scriptName, new TestConfiguration(TEST_CLASS_DIR, TEST_TYPE.FLOOR.scriptName, new String[] { "R" }));
		addTestConfiguration(TEST_TYPE.CEIL.scriptName,  new TestConfiguration(TEST_CLASS_DIR, TEST_TYPE.CEIL.scriptName, new String[] { "R" }));
		addTestConfiguration(TEST_TYPE.CEILING.scriptName,  new TestConfiguration(TEST_CLASS_DIR, TEST_TYPE.CEILING.scriptName, new String[] { "R" }));
	}
	
	@Test
	public void testRound1() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.ROUND, rows1, cols1, sparsity1);
	}
	
	@Test
	public void testRound2() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.ROUND, rows1, cols1, sparsity2);
	}
	
	@Test
	public void testRound3() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.ROUND, rows1, cols1, sparsity3);
	}
	
	@Test
	public void testRound4() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.ROUND, rows2, cols2, sparsity1);
	}
	
	@Test
	public void testRound5() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.ROUND, rows2, cols2, sparsity2);
	}
	
	@Test
	public void testRound6() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.ROUND, rows2, cols2, sparsity3);
	}
	
	@Test
	public void testFloor1() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.FLOOR, rows1, cols1, sparsity1);
	}
	
	@Test
	public void testFloor2() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.FLOOR, rows1, cols1, sparsity2);
	}
	
	@Test
	public void testFloor3() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.FLOOR, rows1, cols1, sparsity3);
	}
	
	@Test
	public void testFloor4() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.FLOOR, rows2, cols2, sparsity1);
	}
	
	@Test
	public void testFloor5() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.FLOOR, rows2, cols2, sparsity2);
	}
	
	@Test
	public void testFloor6() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.FLOOR, rows2, cols2, sparsity3);
	}
	
	@Test
	public void testCeil1() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.CEIL, rows1, cols1, sparsity1);
	}
	
	@Test
	public void testCeil2() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.CEIL, rows1, cols1, sparsity2);
	}
	
	@Test
	public void testCeil3() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.CEIL, rows1, cols1, sparsity3);
	}
	
	@Test
	public void testCeil4() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.CEIL, rows2, cols2, sparsity1);
	}
	
	@Test
	public void testCeil5() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.CEIL, rows2, cols2, sparsity2);
	}
	
	@Test
	public void testCeil6() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.CEIL, rows2, cols2, sparsity3);
	}
	
	@Test
	public void testCeiling1() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.CEILING, rows1, cols1, sparsity1);
	}
	
	@Test
	public void testCeiling2() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.CEILING, rows1, cols1, sparsity2);
	}
	
	@Test
	public void testCeiling3() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.CEILING, rows1, cols1, sparsity3);
	}
	
	@Test
	public void testCeiling4() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.CEILING, rows2, cols2, sparsity1);
	}
	
	@Test
	public void testCeiling5() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.CEILING, rows2, cols2, sparsity2);
	}
	
	@Test
	public void testCeiling6() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.CEILING, rows2, cols2, sparsity3);
	}
	
	@Test
	public void testRoundMR1() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.ROUND, rows1, cols1, sparsity1);
	}
	
	@Test
	public void testRoundMR2() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.ROUND, rows1, cols1, sparsity2);
	}
	
	@Test
	public void testRoundMR3() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.ROUND, rows1, cols1, sparsity3);
	}
	
	@Test
	public void testRoundMR4() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.ROUND, rows2, cols2, sparsity1);
	}
	
	@Test
	public void testRoundMR5() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.ROUND, rows2, cols2, sparsity2);
	}
	
	@Test
	public void testRoundMR6() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.ROUND, rows2, cols2, sparsity3);
	}
	
	@Test
	public void testFloorMR1() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.FLOOR, rows1, cols1, sparsity1);
	}
	
	@Test
	public void testFloorMR2() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.FLOOR, rows1, cols1, sparsity2);
	}
	
	@Test
	public void testFloorMR3() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.FLOOR, rows1, cols1, sparsity3);
	}
	
	@Test
	public void testFloorMR4() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.FLOOR, rows2, cols2, sparsity1);
	}
	
	@Test
	public void testFloorMR5() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.FLOOR, rows2, cols2, sparsity2);
	}
	
	@Test
	public void testFloorMR6() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.FLOOR, rows2, cols2, sparsity3);
	}
	
	@Test
	public void testCeilMR1() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.CEIL, rows1, cols1, sparsity1);
	}
	
	@Test
	public void testCeilMR2() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.CEIL, rows1, cols1, sparsity2);
	}
	
	@Test
	public void testCeilMR3() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.CEIL, rows1, cols1, sparsity3);
	}
	
	@Test
	public void testCeilMR4() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.CEIL, rows2, cols2, sparsity1);
	}
	
	@Test
	public void testCeilMR5() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.CEIL, rows2, cols2, sparsity2);
	}
	
	@Test
	public void testCeilMR6() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.CEIL, rows2, cols2, sparsity3);
	}
	
	@Test
	public void testCeilingMR1() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.CEILING, rows1, cols1, sparsity1);
	}
	
	@Test
	public void testCeilingMR2() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.CEILING, rows1, cols1, sparsity2);
	}
	
	@Test
	public void testCeilingMR3() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.CEILING, rows1, cols1, sparsity3);
	}
	
	@Test
	public void testCeilingMR4() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.CEILING, rows2, cols2, sparsity1);
	}
	
	@Test
	public void testCeilingMR5() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.CEILING, rows2, cols2, sparsity2);
	}
	
	@Test
	public void testCeilingMR6() {
		runTest(RUNTIME_PLATFORM.HYBRID, TEST_TYPE.CEILING, rows2, cols2, sparsity3);
	}
	
	// -----------------------------------------------------------------------------
	
	@Test
	public void testRound1_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.ROUND, rows1, cols1, sparsity1);
	}
	
	@Test
	public void testRound2_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.ROUND, rows1, cols1, sparsity2);
	}
	
	@Test
	public void testRound3_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.ROUND, rows1, cols1, sparsity3);
	}
	
	@Test
	public void testRound4_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.ROUND, rows2, cols2, sparsity1);
	}
	
	@Test
	public void testRound5_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.ROUND, rows2, cols2, sparsity2);
	}
	
	@Test
	public void testRound6_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.ROUND, rows2, cols2, sparsity3);
	}
	
	@Test
	public void testFloor1_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.FLOOR, rows1, cols1, sparsity1);
	}
	
	@Test
	public void testFloor2_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.FLOOR, rows1, cols1, sparsity2);
	}
	
	@Test
	public void testFloor3_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.FLOOR, rows1, cols1, sparsity3);
	}
	
	@Test
	public void testFloor4_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.FLOOR, rows2, cols2, sparsity1);
	}
	
	@Test
	public void testFloor5_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.FLOOR, rows2, cols2, sparsity2);
	}
	
	@Test
	public void testFloor6_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.FLOOR, rows2, cols2, sparsity3);
	}
	
	@Test
	public void testCeil1_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.CEIL, rows1, cols1, sparsity1);
	}
	
	@Test
	public void testCeil2_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.CEIL, rows1, cols1, sparsity2);
	}
	
	@Test
	public void testCeil3_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.CEIL, rows1, cols1, sparsity3);
	}
	
	@Test
	public void testCeil4_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.CEIL, rows2, cols2, sparsity1);
	}
	
	@Test
	public void testCeil5_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.CEIL, rows2, cols2, sparsity2);
	}
	
	@Test
	public void testCeil6_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.CEIL, rows2, cols2, sparsity3);
	}
	
	@Test
	public void testCeiling1_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.CEILING, rows1, cols1, sparsity1);
	}
	
	@Test
	public void testCeiling2_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.CEILING, rows1, cols1, sparsity2);
	}
	
	@Test
	public void testCeiling3_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.CEILING, rows1, cols1, sparsity3);
	}
	
	@Test
	public void testCeiling4_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.CEILING, rows2, cols2, sparsity1);
	}
	
	@Test
	public void testCeiling5_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.CEILING, rows2, cols2, sparsity2);
	}
	
	@Test
	public void testCeiling6_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.CEILING, rows2, cols2, sparsity3);
	}
	
	@Test
	public void testRoundMR1_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.ROUND, rows1, cols1, sparsity1);
	}
	
	@Test
	public void testRoundMR2_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.ROUND, rows1, cols1, sparsity2);
	}
	
	@Test
	public void testRoundMR3_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.ROUND, rows1, cols1, sparsity3);
	}
	
	@Test
	public void testRoundMR4_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.ROUND, rows2, cols2, sparsity1);
	}
	
	@Test
	public void testRoundMR5_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.ROUND, rows2, cols2, sparsity2);
	}
	
	@Test
	public void testRoundMR6_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.ROUND, rows2, cols2, sparsity3);
	}
	
	@Test
	public void testFloorMR1_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.FLOOR, rows1, cols1, sparsity1);
	}
	
	@Test
	public void testFloorMR2_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.FLOOR, rows1, cols1, sparsity2);
	}
	
	@Test
	public void testFloorMR3_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.FLOOR, rows1, cols1, sparsity3);
	}
	
	@Test
	public void testFloorMR4_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.FLOOR, rows2, cols2, sparsity1);
	}
	
	@Test
	public void testFloorMR5_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.FLOOR, rows2, cols2, sparsity2);
	}
	
	@Test
	public void testFloorMR6_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.FLOOR, rows2, cols2, sparsity3);
	}
	
	@Test
	public void testCeilMR1_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.CEIL, rows1, cols1, sparsity1);
	}
	
	@Test
	public void testCeilMR2_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.CEIL, rows1, cols1, sparsity2);
	}
	
	@Test
	public void testCeilMR3_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.CEIL, rows1, cols1, sparsity3);
	}
	
	@Test
	public void testCeilMR4_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.CEIL, rows2, cols2, sparsity1);
	}
	
	@Test
	public void testCeilMR5_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.CEIL, rows2, cols2, sparsity2);
	}
	
	@Test
	public void testCeilMR6_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.CEIL, rows2, cols2, sparsity3);
	}
	
	@Test
	public void testCeilingMR1_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.CEILING, rows1, cols1, sparsity1);
	}
	
	@Test
	public void testCeilingMR2_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.CEILING, rows1, cols1, sparsity2);
	}
	
	@Test
	public void testCeilingMR3_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.CEILING, rows1, cols1, sparsity3);
	}
	
	@Test
	public void testCeilingMR4_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.CEILING, rows2, cols2, sparsity1);
	}
	
	@Test
	public void testCeilingMR5_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.CEILING, rows2, cols2, sparsity2);
	}
	
	@Test
	public void testCeilingMR6_SP() {
		runTest(RUNTIME_PLATFORM.SPARK, TEST_TYPE.CEILING, rows2, cols2, sparsity3);
	}
	
	// -----------------------------------------------------------------------------
	
	private void runTest(RUNTIME_PLATFORM rt, TEST_TYPE test, int rows, int cols, double sparsity) {
		RUNTIME_PLATFORM rtOld = rtplatform;
		rtplatform = rt;
		
		boolean sparkConfigOld = DMLScript.USE_LOCAL_SPARK_CONFIG;
		if( rtplatform == RUNTIME_PLATFORM.SPARK )
			DMLScript.USE_LOCAL_SPARK_CONFIG = true;
	
		try
		{
			TestConfiguration config = getTestConfiguration(test.scriptName);
			config.addVariable("rows", rows);
			config.addVariable("cols", cols);
			loadTestConfiguration(config);
			
			/* This is for running the junit test the new way, i.e., construct the arguments directly */
			String HOME = SCRIPT_DIR + TEST_DIR;
			fullDMLScriptName = HOME + test.scriptName + ".dml";
			programArgs = new String[]{"-args", input("math"), output("R") };
	
			fullRScriptName = HOME + test.scriptName + ".R";
			rCmd = "Rscript" + " " + fullRScriptName + " " + inputDir() + " " + expectedDir();	
			
			long seed = System.nanoTime();
			double[][] matrix = getRandomMatrix(rows, cols, 10, 20, sparsity, seed);
			writeInputMatrixWithMTD("math", matrix, true);
			
			runTest(true, false, null, -1);
			runRScript(true); 
	
			TestUtils.compareDMLHDFSFileWithRFile(expected("R"), output("R"), 1e-9);
		}
		finally {
			DMLScript.USE_LOCAL_SPARK_CONFIG = sparkConfigOld;
			
			//reset runtime platform
			rtplatform = rtOld;
		}
	}
}

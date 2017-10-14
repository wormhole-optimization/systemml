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

import java.util.HashMap;
import java.util.Random;

import org.junit.Assert;
import org.junit.Test;

import org.apache.sysml.api.DMLScript;
import org.apache.sysml.api.DMLScript.RUNTIME_PLATFORM;
import org.apache.sysml.lops.LopProperties.ExecType;
import org.apache.sysml.runtime.matrix.data.MatrixValue.CellIndex;
import org.apache.sysml.test.integration.AutomatedTestBase;
import org.apache.sysml.test.integration.TestConfiguration;
import org.apache.sysml.test.utils.TestUtils;
import org.apache.sysml.utils.Statistics;

public class ReplaceTest extends AutomatedTestBase 
{
	private final static String TEST_NAME1 = "replace_value";
	private final static String TEST_NAME2 = "replace_NaN";
	private final static String TEST_NAME3 = "replace_Infinity";
	private final static String TEST_NAME4 = "replace_NInfinity";
	private final static String TEST_NAME5 = "replace_maxmin";
	
	private final static String TEST_DIR = "functions/unary/matrix/";
	private static final String TEST_CLASS_DIR = TEST_DIR + ReplaceTest.class.getSimpleName() + "/";

	private final static int rows = 1577;
	private final static int cols = 37;
	
	private final static double sparsity1 = 0.7;
	private final static double sparsity2 = 0.07;
	
	@Override
	public void setUp() 
	{
		addTestConfiguration(TEST_NAME1, 
				new TestConfiguration(TEST_CLASS_DIR, TEST_NAME1, new String[] { "C" }) ); 
		addTestConfiguration(TEST_NAME2, 
				new TestConfiguration(TEST_CLASS_DIR, TEST_NAME2, new String[] { "C" }) ); 
		addTestConfiguration(TEST_NAME3, 
				new TestConfiguration(TEST_CLASS_DIR, TEST_NAME3, new String[] { "C" }) ); 
		addTestConfiguration(TEST_NAME4, 
				new TestConfiguration(TEST_CLASS_DIR, TEST_NAME4, new String[] { "C" }) ); 
		addTestConfiguration(TEST_NAME5, 
				new TestConfiguration(TEST_CLASS_DIR, TEST_NAME5, new String[] { "C" }) ); 
	}
	
	@Test
	public void testReplaceZeroDenseCP() 
	{
		runTestReplace( TEST_NAME1, 0, false, ExecType.CP );
	}
	
	@Test
	public void testReplaceValueDenseCP() 
	{
		runTestReplace( TEST_NAME1, 7, false, ExecType.CP );
	}
	
	@Test
	public void testReplaceNaNDenseCP() 
	{
		runTestReplace( TEST_NAME2, Double.NaN, false, ExecType.CP );
	}
	
	@Test
	public void testReplacePInfinityDenseCP() 
	{
		runTestReplace( TEST_NAME3, Double.POSITIVE_INFINITY, false, ExecType.CP );
	}
	
	@Test
	public void testReplaceNInfinityDenseCP() 
	{
		runTestReplace( TEST_NAME4, Double.NEGATIVE_INFINITY, false, ExecType.CP );
	}
	
	@Test
	public void testReplaceMaxMinDenseCP() 
	{
		runTestReplace( TEST_NAME5, -1, false, ExecType.CP );
	}

	@Test
	public void testReplaceZeroSparseCP() 
	{
		runTestReplace( TEST_NAME1, 0, true, ExecType.CP );
	}
	
	@Test
	public void testReplaceValueSparseCP() 
	{
		runTestReplace( TEST_NAME1, 7, true, ExecType.CP );
	}
	
	@Test
	public void testReplaceNaNSparseCP() 
	{
		runTestReplace( TEST_NAME2, Double.NaN, true, ExecType.CP );
	}
	
	@Test
	public void testReplacePInfinitySparseCP() 
	{
		runTestReplace( TEST_NAME3, Double.POSITIVE_INFINITY, true, ExecType.CP );
	}
	
	@Test
	public void testReplaceNInfinitySparseCP() 
	{
		runTestReplace( TEST_NAME4, Double.NEGATIVE_INFINITY, true, ExecType.CP );
	}
	
	@Test
	public void testReplaceMaxMinSparseCP() 
	{
		runTestReplace( TEST_NAME5, -1, true, ExecType.CP );
	}
	
	// ------------------------------------------------------------------------

	@Test
	public void testReplaceZeroDenseSP() 
	{	
		runTestReplace( TEST_NAME1, 0, false, ExecType.SPARK );
	}
	
	@Test
	public void testReplaceValueDenseSP() 
	{	
		runTestReplace( TEST_NAME1, 7, false, ExecType.SPARK );
	}
	
	@Test
	public void testReplaceNaNDenseSP() 
	{	
		runTestReplace( TEST_NAME2, Double.NaN, false, ExecType.SPARK );
	}
	
	@Test
	public void testReplacePInfinityDenseSP() 
	{	
		runTestReplace( TEST_NAME3, Double.POSITIVE_INFINITY, false, ExecType.SPARK );
	}
	
	@Test
	public void testReplaceNInfinityDenseSP() 
	{	
		runTestReplace( TEST_NAME4, Double.NEGATIVE_INFINITY, false, ExecType.SPARK );
	}
	
	@Test
	public void testReplaceMaxMinDenseSP() 
	{	
		runTestReplace( TEST_NAME5, -1, false, ExecType.SPARK );
	}

	@Test
	public void testReplaceZeroSparseSP() 
	{
		runTestReplace( TEST_NAME1, 0, true, ExecType.SPARK );
	}
	
	@Test
	public void testReplaceValueSparseSP() 
	{	
		runTestReplace( TEST_NAME1, 7, true, ExecType.SPARK );
	}
	
	@Test
	public void testReplaceNaNSparseSP() 
	{
		runTestReplace( TEST_NAME2, Double.NaN, true, ExecType.SPARK );
	}
	
	@Test
	public void testReplacePInfinitySparseSP() 
	{
		runTestReplace( TEST_NAME3, Double.POSITIVE_INFINITY, true, ExecType.SPARK );
	}
	
	@Test
	public void testReplaceNInfinitySparseSP() 
	{
		runTestReplace( TEST_NAME4, Double.NEGATIVE_INFINITY, true, ExecType.SPARK );
	}
	
	@Test
	public void testReplaceMaxMinSparseSP() 
	{
		runTestReplace( TEST_NAME5, -1, true, ExecType.SPARK );
	}
	
	// ------------------------------------------------------------------------
	
	@Test
	public void testReplaceZeroDenseMR() 
	{
		runTestReplace( TEST_NAME1, 0, false, ExecType.MR );
	}
	
	@Test
	public void testReplaceValueDenseMR() 
	{
		runTestReplace( TEST_NAME1, 7, false, ExecType.MR );
	}
	
	@Test
	public void testReplaceNaNDenseMR() 
	{
		runTestReplace( TEST_NAME2, Double.NaN, false, ExecType.MR );
	}
	
	@Test
	public void testReplacePInfinityDenseMR() 
	{
		runTestReplace( TEST_NAME3, Double.POSITIVE_INFINITY, false, ExecType.MR );
	}
	
	@Test
	public void testReplaceNInfinityDenseMR() 
	{
		runTestReplace( TEST_NAME4, Double.NEGATIVE_INFINITY, false, ExecType.MR );
	}
	
	@Test
	public void testReplaceMaxMinDenseMR() 
	{
		runTestReplace( TEST_NAME5, -1, false, ExecType.MR );
	}

	@Test
	public void testReplaceZeroSparseMR() 
	{
		runTestReplace( TEST_NAME1, 0, true, ExecType.MR );
	}
	
	@Test
	public void testReplaceValueSparseMR() 
	{
		runTestReplace( TEST_NAME1, 7, true, ExecType.MR );
	}
	
	@Test
	public void testReplaceNaNSparseMR() 
	{
		runTestReplace( TEST_NAME2, Double.NaN, true, ExecType.MR );
	}
	
	@Test
	public void testReplacePInfinitySparseMR() 
	{
		runTestReplace( TEST_NAME3, Double.POSITIVE_INFINITY, true, ExecType.MR );
	}
	
	@Test
	public void testReplaceNInfinitySparseMR() 
	{
		runTestReplace( TEST_NAME4, Double.NEGATIVE_INFINITY, true, ExecType.MR );
	}
	
	@Test
	public void testReplaceMaxMinSparseMR() 
	{
		runTestReplace( TEST_NAME5, -1, true, ExecType.MR );
	}
		
	/**
	 * 
	 * @param test
	 * @param pattern
	 * @param sparse
	 * @param etype
	 */
	private void runTestReplace( String test, double pattern, boolean sparse, ExecType etype )
	{		
		RUNTIME_PLATFORM platformOld = rtplatform;
		boolean sparkConfigOld = DMLScript.USE_LOCAL_SPARK_CONFIG;
		
		try
		{
			if(etype == ExecType.SPARK) {
		    	rtplatform = RUNTIME_PLATFORM.SPARK;
		    }
		    else {
		    	rtplatform = (etype==ExecType.MR)? RUNTIME_PLATFORM.HADOOP : RUNTIME_PLATFORM.HYBRID;
		    }
			if( rtplatform == RUNTIME_PLATFORM.SPARK )
				DMLScript.USE_LOCAL_SPARK_CONFIG = true;
			
			double sparsity = (sparse)? sparsity2 : sparsity1;
				
			//register test configuration
			TestConfiguration config = getTestConfiguration(test);
			config.addVariable("rows", rows);
			config.addVariable("cols", cols);
			loadTestConfiguration(config);
			
			String HOME = SCRIPT_DIR + TEST_DIR;
			fullDMLScriptName = HOME + test + ".dml";
			programArgs = new String[]{"-args", input("A"), String.valueOf(rows), String.valueOf(cols), 
				output("C"), String.valueOf(pattern) }; //only respected for TEST_NAME1
			
			fullRScriptName = HOME + test + ".R";
			rCmd = "Rscript" + " " + fullRScriptName + " " + inputDir() + " " + 
				pattern + " " + expectedDir();
			
			double[][] A = getRandomMatrix(rows, cols, 0, 1, sparsity, 7);
			replaceRandom(A, rows, cols, pattern, 10);	
	        writeInputMatrix("A", A, true);
			writeExpectedMatrix("A", A);

			runTest(true, false, null, -1);
			runRScript(true); 
		
			int numMRExpect = (etype==ExecType.MR)?(test.equals(TEST_NAME1)?1:test.equals(TEST_NAME5)?3:2):0; 
			Assert.assertEquals("Unexpected number of executed MR jobs.", 
		           numMRExpect, Statistics.getNoOfExecutedMRJobs()); //reblock in test1, reblock+GMR in test2-4
		
			//compare matrices 
			HashMap<CellIndex, Double> dmlfile = readDMLMatrixFromHDFS("C");
			HashMap<CellIndex, Double> rfile  = readRMatrixFromFS("C");
			TestUtils.compareMatrices(dmlfile, rfile, 1e-14, "Stat-DML", "Stat-R");
			
		}
		finally
		{
			//reset platform for additional tests
			rtplatform = platformOld;
			DMLScript.USE_LOCAL_SPARK_CONFIG = sparkConfigOld;
		}
	}
	
	private static void replaceRandom( double[][] A, int rows, int cols, double replacement, int len ) {
		Random rand = new Random();
		for( int i=0; i<len; i++ )
			A[rand.nextInt(rows-1)][rand.nextInt(cols-1)] = replacement;
	}
}
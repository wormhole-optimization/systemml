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
package org.apache.sysml.test.integration.functions.tensor;

import java.util.HashMap;

import org.apache.sysml.api.DMLScript;
import org.apache.sysml.api.DMLScript.RUNTIME_PLATFORM;
import org.apache.sysml.lops.LopProperties.ExecType;
import org.apache.sysml.runtime.matrix.data.MatrixValue.CellIndex;
import org.apache.sysml.runtime.util.ConvolutionUtils;
import org.apache.sysml.test.integration.AutomatedTestBase;
import org.apache.sysml.test.integration.TestConfiguration;
import org.apache.sysml.test.utils.TestUtils;
import org.junit.Test;

public class Conv2DBackwardTest extends AutomatedTestBase
{
	private final static String TEST_NAME = "Conv2DBackwardTest";
	private final static String TEST_DIR = "functions/tensor/";
	private final static String TEST_CLASS_DIR = TEST_DIR + Conv2DBackwardTest.class.getSimpleName() + "/";
	private final static double epsilon=0.0000000001;
	
	@Override
	public void setUp() {
		TestUtils.clearAssertionInformation();
		addTestConfiguration(TEST_NAME, new TestConfiguration(TEST_CLASS_DIR, TEST_NAME, new String[] {"B"}));
	}
	
	
	@Test
	public void testConv2DBackwardFilterDense1() {
		int numImg = 3; int imgSize = 3; int numChannels = 3; int numFilters = 1; int filterSize = 2; int stride = 1; int pad = 0;
		runConv2DBackwardFilterTest(ExecType.CP, imgSize, numImg, numChannels, numFilters, filterSize, stride, pad, false, false);
	}
	
	@Test
	public void testConv2DBackwardFilterDense2() {
		int numImg = 3; int imgSize = 3; int numChannels = 3; int numFilters = 4; int filterSize = 2; int stride = 1; int pad = 0;
		runConv2DBackwardFilterTest(ExecType.CP, imgSize, numImg, numChannels, numFilters, filterSize, stride, pad, false, false);
	}
	
	@Test
	public void testConv2DBackwardFilterDense3() {
		int numImg = 3; int imgSize = 10; int numChannels = 4; int numFilters = 3; int filterSize = 2; int stride = 2; int pad = 1;
		runConv2DBackwardFilterTest(ExecType.CP, imgSize, numImg, numChannels, numFilters, filterSize, stride, pad, false, false);
	}
	
	@Test
	public void testConv2DBackwardFilterDense4() {
		int numImg = 3; int imgSize = 10; int numChannels = 4; int numFilters = 3; int filterSize = 5; int stride = 1; int pad = 1;
		runConv2DBackwardFilterTest(ExecType.CP, imgSize, numImg, numChannels, numFilters, filterSize, stride, pad, false, false);
	}
	
	@Test
	public void testConv2DBackwardFilterDense5() {
		int numImg = 3; int imgSize = 10; int numChannels = 2; int numFilters = 3; int filterSize = 5; int stride = 3; int pad = 2;
		runConv2DBackwardFilterTest(ExecType.CP, imgSize, numImg, numChannels, numFilters, filterSize, stride, pad, false, false);
	}
	
	@Test
	public void testConv2DBackwardFilterSparse1() {
		int numImg = 3; int imgSize = 3; int numChannels = 3; int numFilters = 1; int filterSize = 2; int stride = 1; int pad = 0;
		runConv2DBackwardFilterTest(ExecType.CP, imgSize, numImg, numChannels, numFilters, filterSize, stride, pad, false, true);
	}
	
	@Test
	public void testConv2DBackwardFilterSparse2() {
		int numImg = 3; int imgSize = 3; int numChannels = 3; int numFilters = 4; int filterSize = 2; int stride = 1; int pad = 0;
		runConv2DBackwardFilterTest(ExecType.CP, imgSize, numImg, numChannels, numFilters, filterSize, stride, pad, false, true);
	}
	
	@Test
	public void testConv2DBackwardFilterSparse3() {
		int numImg = 3; int imgSize = 10; int numChannels = 4; int numFilters = 3; int filterSize = 2; int stride = 2; int pad = 1;
		runConv2DBackwardFilterTest(ExecType.CP, imgSize, numImg, numChannels, numFilters, filterSize, stride, pad, false, true);
	}
	
	@Test
	public void testConv2DBackwardFilterSparse4() {
		int numImg = 3; int imgSize = 10; int numChannels = 4; int numFilters = 3; int filterSize = 5; int stride = 1; int pad = 1;
		runConv2DBackwardFilterTest(ExecType.CP, imgSize, numImg, numChannels, numFilters, filterSize, stride, pad, false, true);
	}
	
	@Test
	public void testConv2DBackwardFilterSparse5() {
		int numImg = 3; int imgSize = 10; int numChannels = 2; int numFilters = 3; int filterSize = 5; int stride = 3; int pad = 2;
		runConv2DBackwardFilterTest(ExecType.CP, imgSize, numImg, numChannels, numFilters, filterSize, stride, pad, false, true);
	}
	
	@Test
	public void testConv2DBackwardFilterSparse6() {
		int numImg = 3; int imgSize = 3; int numChannels = 3; int numFilters = 1; int filterSize = 2; int stride = 1; int pad = 0;
		runConv2DBackwardFilterTest(ExecType.CP, imgSize, numImg, numChannels, numFilters, filterSize, stride, pad, true, false);
	}
	
	@Test
	public void testConv2DBackwardFilterSparse7() {
		int numImg = 3; int imgSize = 3; int numChannels = 3; int numFilters = 4; int filterSize = 2; int stride = 1; int pad = 0;
		runConv2DBackwardFilterTest(ExecType.CP, imgSize, numImg, numChannels, numFilters, filterSize, stride, pad, true, false);
	}
	
	@Test
	public void testConv2DBackwardFilterSparse8() {
		int numImg = 3; int imgSize = 10; int numChannels = 4; int numFilters = 3; int filterSize = 2; int stride = 2; int pad = 1;
		runConv2DBackwardFilterTest(ExecType.CP, imgSize, numImg, numChannels, numFilters, filterSize, stride, pad, true, false);
	}
	
	@Test
	public void testConv2DBackwardFilterSparse9() {
		int numImg = 3; int imgSize = 10; int numChannels = 4; int numFilters = 3; int filterSize = 5; int stride = 1; int pad = 1;
		runConv2DBackwardFilterTest(ExecType.CP, imgSize, numImg, numChannels, numFilters, filterSize, stride, pad, true, false);
	}
	
	@Test
	public void testConv2DBackwardFilterSparse10() {
		int numImg = 3; int imgSize = 10; int numChannels = 2; int numFilters = 3; int filterSize = 5; int stride = 3; int pad = 2;
		runConv2DBackwardFilterTest(ExecType.CP, imgSize, numImg, numChannels, numFilters, filterSize, stride, pad, true, false);
	}
	
	@Test
	public void testConv2DBackwardFilterSparse11() {
		int numImg = 3; int imgSize = 3; int numChannels = 3; int numFilters = 1; int filterSize = 2; int stride = 1; int pad = 0;
		runConv2DBackwardFilterTest(ExecType.CP, imgSize, numImg, numChannels, numFilters, filterSize, stride, pad, true, true);
	}
	
	@Test
	public void testConv2DBackwardFilterSparse12() {
		int numImg = 3; int imgSize = 3; int numChannels = 3; int numFilters = 4; int filterSize = 2; int stride = 1; int pad = 0;
		runConv2DBackwardFilterTest(ExecType.CP, imgSize, numImg, numChannels, numFilters, filterSize, stride, pad, true, true);
	}
	
	@Test
	public void testConv2DBackwardFilterSparse13() {
		int numImg = 3; int imgSize = 10; int numChannels = 4; int numFilters = 3; int filterSize = 2; int stride = 2; int pad = 1;
		runConv2DBackwardFilterTest(ExecType.CP, imgSize, numImg, numChannels, numFilters, filterSize, stride, pad, true, true);
	}
	
	@Test
	public void testConv2DBackwardFilterSparse14() {
		int numImg = 3; int imgSize = 10; int numChannels = 4; int numFilters = 3; int filterSize = 5; int stride = 1; int pad = 1;
		runConv2DBackwardFilterTest(ExecType.CP, imgSize, numImg, numChannels, numFilters, filterSize, stride, pad, true, true);
	}
	
	@Test
	public void testConv2DBackwardFilterSparse15() {
		int numImg = 3; int imgSize = 10; int numChannels = 2; int numFilters = 3; int filterSize = 5; int stride = 3; int pad = 2;
		runConv2DBackwardFilterTest(ExecType.CP, imgSize, numImg, numChannels, numFilters, filterSize, stride, pad, true, false);
	}
	
	@Test
	public void testConv2DBackwardFilterSparse16() {
		int numImg = 10; int imgSize = 40; int numChannels = 4; int numFilters = 30; int filterSize = 25; int stride = 1; int pad = 0;
		runConv2DBackwardFilterTest(ExecType.CP, imgSize, numImg, numChannels, numFilters, filterSize, stride, pad, true, false);
	}
	
	@Test
	public void testConv2DBackwardFilterSparse17() {
		int numImg = 10, imgSize = 40, numChannels = 4, numFilters = 30, filterSize = 25, stride = 1, pad = 0;
		runConv2DBackwardFilterTest(ExecType.CP, imgSize, numImg, numChannels, numFilters, filterSize, stride, pad, false, true);
	}
	
	public void runConv2DBackwardFilterTest( ExecType et, int imgSize, int numImg, int numChannels, int numFilters, 
		int filterSize, int stride, int pad, boolean sparse1, boolean sparse2) 
	{
		RUNTIME_PLATFORM platformOld = rtplatform;
		switch( et ){
			case MR: rtplatform = RUNTIME_PLATFORM.HADOOP; break;
			case SPARK: rtplatform = RUNTIME_PLATFORM.SPARK; break;
			default: rtplatform = RUNTIME_PLATFORM.HYBRID; break;
		}
		boolean sparkConfigOld = DMLScript.USE_LOCAL_SPARK_CONFIG;
		if( rtplatform == RUNTIME_PLATFORM.SPARK )
			DMLScript.USE_LOCAL_SPARK_CONFIG = true;
		
		try
		{
			String sparseVal1 = String.valueOf(sparse1).toUpperCase();
			String sparseVal2 = String.valueOf(sparse2).toUpperCase();
			long P = ConvolutionUtils.getP(imgSize, filterSize, stride, pad);
			TestConfiguration config = getTestConfiguration(TEST_NAME);
			loadTestConfiguration(config);
			
			String RI_HOME = SCRIPT_DIR + TEST_DIR;
			fullDMLScriptName = RI_HOME + TEST_NAME + ".dml";
			programArgs = new String[]{"-explain", "-args", 
				String.valueOf(imgSize), String.valueOf(numImg), 
				String.valueOf(numChannels), String.valueOf(numFilters), 
				String.valueOf(filterSize), String.valueOf(stride), String.valueOf(pad), 
				String.valueOf(P), String.valueOf(P), output("B"), sparseVal1, sparseVal2};
			fullRScriptName = RI_HOME + TEST_NAME + ".R";
			rCmd = "Rscript" + " " + fullRScriptName + " " + imgSize + " " + numImg + 
					" " + numChannels + " " + numFilters + 
					" " + filterSize + " " + stride + " " + pad + " " + P + " " + P + " " + expectedDir() +
					" " + sparseVal1 + " " + sparseVal2;
			
			// Run DML and R scripts
			runTest(true, false, null, -1);
			runRScript(true);
			
			HashMap<CellIndex, Double> bHM = readRMatrixFromFS("B");
			HashMap<CellIndex, Double> dmlfile = readDMLMatrixFromHDFS("B");
			TestUtils.compareMatrices(dmlfile, bHM, epsilon, "B-DML", "NumPy");
		}
		finally {
			rtplatform = platformOld;
			DMLScript.USE_LOCAL_SPARK_CONFIG = sparkConfigOld;
		}
	}
}

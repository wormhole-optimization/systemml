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

package org.apache.sysml.test.integration.functions.recompile;

import java.util.HashMap;

import org.junit.Assert;
import org.junit.Test;
import org.apache.sysml.conf.CompilerConfig;
import org.apache.sysml.hops.OptimizerUtils;
import org.apache.sysml.parser.Expression.ValueType;
import org.apache.sysml.runtime.matrix.MatrixCharacteristics;
import org.apache.sysml.runtime.matrix.data.MatrixBlock;
import org.apache.sysml.runtime.matrix.data.OutputInfo;
import org.apache.sysml.runtime.matrix.data.MatrixValue.CellIndex;
import org.apache.sysml.runtime.util.DataConverter;
import org.apache.sysml.runtime.util.MapReduceTool;
import org.apache.sysml.test.integration.AutomatedTestBase;
import org.apache.sysml.test.integration.TestConfiguration;
import org.apache.sysml.test.utils.TestUtils;
import org.apache.sysml.utils.Statistics;

public class SparsityRecompileTest extends AutomatedTestBase 
{
	private final static String TEST_DIR = "functions/recompile/";
	private final static String TEST_NAME1 = "while_recompile_sparse";
	private final static String TEST_NAME2 = "if_recompile_sparse";
	private final static String TEST_NAME3 = "for_recompile_sparse";
	private final static String TEST_NAME4 = "parfor_recompile_sparse";
	private final static String TEST_CLASS_DIR = TEST_DIR + SparsityRecompileTest.class.getSimpleName() + "/";
	
	private final static long rows = 1000;
	private final static long cols = 500000;
	private final static double sparsity = 0.00001d;
	private final static double val = 7.0;
	
	@Override
	public void setUp() 
	{
		TestUtils.clearAssertionInformation();
		addTestConfiguration(TEST_NAME1, 
			new TestConfiguration(TEST_CLASS_DIR, TEST_NAME1, new String[] { "Rout" }) );
		addTestConfiguration(TEST_NAME2, 
			new TestConfiguration(TEST_CLASS_DIR, TEST_NAME2, new String[] { "Rout" }) );
		addTestConfiguration(TEST_NAME3, 
			new TestConfiguration(TEST_CLASS_DIR, TEST_NAME3, new String[] { "Rout" }) );
		addTestConfiguration(TEST_NAME4, 
			new TestConfiguration(TEST_CLASS_DIR, TEST_NAME4, new String[] { "Rout" }) );
	}

	@Test
	public void testWhileRecompile() 
	{
		runRecompileTest(TEST_NAME1, true);
	}
	
	@Test
	public void testWhileNoRecompile() 
	{
		runRecompileTest(TEST_NAME1, false);
	}
	
	@Test
	public void testIfRecompile() 
	{
		runRecompileTest(TEST_NAME2, true);
	}
	
	@Test
	public void testIfNoRecompile() 
	{
		runRecompileTest(TEST_NAME2, false);
	}
	
	@Test
	public void testForRecompile() 
	{
		runRecompileTest(TEST_NAME3, true);
	}
	
	@Test
	public void testForNoRecompile() 
	{
		runRecompileTest(TEST_NAME3, false);
	}
	
	@Test
	public void testParForRecompile() 
	{
		runRecompileTest(TEST_NAME4, true);
	}
	
	@Test
	public void testParForNoRecompile() 
	{
		runRecompileTest(TEST_NAME4, false);
	}

	
	private void runRecompileTest( String testname, boolean recompile )
	{	
		boolean oldFlagRecompile = CompilerConfig.FLAG_DYN_RECOMPILE;
		
		try
		{
			getAndLoadTestConfiguration(testname);
			
			String HOME = SCRIPT_DIR + TEST_DIR;
			fullDMLScriptName = HOME + testname + ".dml";
			programArgs = new String[]{"-explain", "-args",
				input("V"), Double.toString(val), output("R") };

			CompilerConfig.FLAG_DYN_RECOMPILE = recompile;
			
			MatrixBlock mb = MatrixBlock.randOperations((int)rows, (int)cols, sparsity, 0, 1, "uniform", System.currentTimeMillis());
			MatrixCharacteristics mc = new MatrixCharacteristics(rows,cols,OptimizerUtils.DEFAULT_BLOCKSIZE,OptimizerUtils.DEFAULT_BLOCKSIZE,(long)(rows*cols*sparsity));
			
			DataConverter.writeMatrixToHDFS(mb, input("V"), OutputInfo.TextCellOutputInfo, mc);
			MapReduceTool.writeMetaDataFile(input("V.mtd"), ValueType.DOUBLE, mc, OutputInfo.TextCellOutputInfo);
			
			boolean exceptionExpected = false;
			runTest(true, exceptionExpected, null, -1); 
			
			//CHECK compiled MR jobs
			int expectNumCompiled =   (testname.equals(TEST_NAME2)?3:4) //reblock,GMR,GMR,GMR (one GMR less for if) 
	                                + (testname.equals(TEST_NAME4)?2:0);//(+2 resultmerge)
			Assert.assertEquals("Unexpected number of compiled MR jobs.", 
					            expectNumCompiled, Statistics.getNoOfCompiledMRJobs());
		
			//CHECK executed MR jobs
			int expectNumExecuted = -1;
			if( recompile ) expectNumExecuted = 0 + ((testname.equals(TEST_NAME4))?2:0); //(+2 resultmerge) 
			else            expectNumExecuted =  (testname.equals(TEST_NAME2)?3:4) //reblock,GMR,GMR,GMR (one GMR less for if)
					                              + ((testname.equals(TEST_NAME4))?2:0); //(+2 resultmerge) 
			Assert.assertEquals("Unexpected number of executed MR jobs.", 
		                        expectNumExecuted, Statistics.getNoOfExecutedMRJobs());

			
			//compare matrices
			HashMap<CellIndex, Double> dmlfile = readDMLMatrixFromHDFS("R");
			Assert.assertEquals((Double)val, dmlfile.get(new CellIndex(1,1)));
		}
		catch(Exception ex)
		{
			throw new RuntimeException(ex);
			//Assert.fail("Failed to run test: "+ex.getMessage());
		}
		finally
		{
			CompilerConfig.FLAG_DYN_RECOMPILE = oldFlagRecompile;
		}
	}
	
}
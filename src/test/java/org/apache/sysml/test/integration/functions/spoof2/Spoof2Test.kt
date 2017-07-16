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

package org.apache.sysml.test.integration.functions.spoof2

import org.apache.sysml.api.DMLScript
import org.apache.sysml.hops.OptimizerUtils
import org.apache.sysml.lops.LopProperties
import org.apache.sysml.lops.LopProperties.ExecType
import org.apache.sysml.lops.LopProperties.ExecType.*
import org.apache.sysml.test.integration.AutomatedTestBase
import org.apache.sysml.test.integration.TestConfiguration
import org.apache.sysml.test.utils.TestUtils
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import java.io.File

@RunWith(Parameterized::class)
class Spoof2Test(
        private val testName: String,
        private val rewrites: Boolean,
        private val execType: ExecType
) : AutomatedTestBase() {

    companion object {
        private const val TEST_NAME = "spoof2pattern"
        //	TEST_NAME+ 1;  //t(X)
        //	TEST_NAME+ 2;  //rowSum(t(X))
        //	TEST_NAME+ 3;  //colSum(t(X))
        //	TEST_NAME+ 4;  //sum(t(X))
        //	TEST_NAME+ 5;  //X%*%Y
        //	TEST_NAME+ 6;  //t(t(X)%*%t(Y))
        //	TEST_NAME+ 7;  //rowSums(t(t(X)%*%t(Y)))
        //	TEST_NAME+ 8;  //colSums(t(t(X)%*%t(Y)))
        //	TEST_NAME+ 9;  //t(X)%*%(w*(Y%*%v))
        //	TEST_NAME+10;  //2-X
        //	TEST_NAME+11;  //t(X)%*%(2-(w*(Y%*%v)))
        //	TEST_NAME+12;  //print(sum(v))                  // print expects a scalar
        //	TEST_NAME+13;  //x%*%y                          // inner product
        //	TEST_NAME+14;  //x%*%y                          // outer product
        //	TEST_NAME+15;  //rowIndexMax(X)
        //	TEST_NAME+16;  //rowIndexMax(t(X))
        //	TEST_NAME+17;  //t(rowIndexMax(t(X)))
        //	TEST_NAME+18;  //t(t(X))
        //	TEST_NAME+19;  //t(X)%*%(Y%*%y)  // this rewrites to t(X%*%t(Y%*%y)), which is normally good (tranpose the vector rather than the matrix) but messes up a fusion pattern
        //	TEST_NAME+20;  //sum(X)*Y
        //	TEST_NAME+21;  //X*Y*Z
        //	TEST_NAME+22;  //X%*%Y%*%Z;
        //	TEST_NAME+23;  //CSE
        //	TEST_NAME+24;  //sum(X%*%Y)
        //	TEST_NAME+25;  //sum( (U%*%t(V))^2 ) // need common subexpression splitting, power-to-multiply
        //	TEST_NAME+26;  //X * (r %*% M %*% c) // the right multiply results in a scalar; the sum-product block can be partitioned
        //	TEST_NAME+27;  //((X * X) %*% Y) * Z
        //	TEST_NAME+28;  //((X * X) %*% Y)
        //	TEST_NAME+29;  //((X * X^2.2) %*% Y)
        //	TEST_NAME+30;  //((X * Z) %*% Y)
        private const val NUM_TESTS = 31

        private const val TEST_DIR = "functions/spoof2/"
        private val TEST_CLASS_DIR = TEST_DIR + Spoof2Test::class.java.simpleName + "/"
        private const val TEST_CONF_SPOOF2 = "SystemML-config-spoof2.xml"
        private const val TEST_CONF_NOSPOOF2 = "SystemML-config-nospoof2.xml"
        private val TEST_CONF_FILE_SPOOF2 = File(SCRIPT_DIR + TEST_DIR, TEST_CONF_SPOOF2)
        private val TEST_CONF_FILE_NOSPOOF2 = File(SCRIPT_DIR + TEST_DIR, TEST_CONF_NOSPOOF2)

        private const val eps = 10.0e-10

        @JvmStatic
        @Parameterized.Parameters(name = "testSpoof2({0}, rewrites={1}, {2})")
        fun testParams(): Collection<Array<Any>> {
            val params = ArrayList<Array<Any>>(NUM_TESTS * 3)
            for (testNum in 1..NUM_TESTS) {
//                if (testNum != NUM_TESTS) continue

                val testName = TEST_NAME + testNum
//                params.add(arrayOf(testName, false, CP))
//                params.add(arrayOf(testName, false, SPARK))
                params.add(arrayOf(testName, true, CP))
            }
            return params
        }
    }

    override fun setUp() {
        TestUtils.clearAssertionInformation()
        for (i in 1..NUM_TESTS)
            addTestConfiguration(TEST_NAME + i, TestConfiguration(TEST_CLASS_DIR, TEST_NAME + i, arrayOf(i.toString())))
    }

    @Test
    fun test() {
        testIt(testName, rewrites, execType)
    }


    private fun testIt(testname: String, rewrites: Boolean, instType: LopProperties.ExecType) {
        val oldFlag = OptimizerUtils.ALLOW_ALGEBRAIC_SIMPLIFICATION
        val platformOld = AutomatedTestBase.rtplatform
        when (instType) {
            MR -> AutomatedTestBase.rtplatform = DMLScript.RUNTIME_PLATFORM.HADOOP
            SPARK -> AutomatedTestBase.rtplatform = DMLScript.RUNTIME_PLATFORM.SPARK
            else -> AutomatedTestBase.rtplatform = DMLScript.RUNTIME_PLATFORM.HYBRID_SPARK
        }

        val sparkConfigOld = DMLScript.USE_LOCAL_SPARK_CONFIG
        if (AutomatedTestBase.rtplatform == DMLScript.RUNTIME_PLATFORM.SPARK || AutomatedTestBase.rtplatform == DMLScript.RUNTIME_PLATFORM.HYBRID_SPARK)
            DMLScript.USE_LOCAL_SPARK_CONFIG = true

        try {
            val config = getTestConfiguration(testname)
            loadTestConfiguration(config)

            val HOME = AutomatedTestBase.SCRIPT_DIR + TEST_DIR
            fullDMLScriptName = HOME + testname + ".dml"
            if ( rewrites ) // "-explain", "recompile_hops",
            programArgs = arrayOf("-stats", "-args", output("S"))


            fullRScriptName = HOME + testname + ".R"
            rCmd = getRCmd(inputDir(), expectedDir())

            runTest(true, false, null, -1)
            runRScript(true)

            //compare matrices
            val dmlfile = AutomatedTestBase.readDMLMatrixFromHDFS("S")
            val rfile = readRMatrixFromFS("S")
            TestUtils.compareMatrices(dmlfile, rfile, eps, "Stat-DML", "Stat-R")

//            Assert.assertTrue(heavyHittersContainsSubString("spoofRA") || heavyHittersContainsSubString("sp_spoofRA"))

            //ensure full aggregates for certain patterns
//            if (testname == TEST_NAME+15)
//                Assert.assertTrue(!heavyHittersContainsSubString("uark+"))
//            if (testname == TEST_NAME+17)
//                Assert.assertTrue(!heavyHittersContainsSubString("rangeReIndex"))

        } finally {
            AutomatedTestBase.rtplatform = platformOld
            DMLScript.USE_LOCAL_SPARK_CONFIG = sparkConfigOld
            OptimizerUtils.ALLOW_ALGEBRAIC_SIMPLIFICATION = oldFlag
            OptimizerUtils.ALLOW_AUTO_VECTORIZATION = true
            OptimizerUtils.ALLOW_OPERATOR_FUSION = true
        }
    }

    /**
     * Override default configuration with custom test configuration to ensure
     * scratch space and local temporary directory locations are also updated.
     */
    override fun getConfigTemplateFile(): File {
        // Instrumentation in this test's output log to show custom configuration file used for template.
        val tcf = if( rewrites ) TEST_CONF_FILE_SPOOF2 else TEST_CONF_FILE_NOSPOOF2
        println("This test case overrides default configuration with " + tcf.path)
        return tcf
    }


}

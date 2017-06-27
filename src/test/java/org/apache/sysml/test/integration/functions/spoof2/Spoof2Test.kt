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
import org.junit.Assert
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
        private const val NUM_TESTS = 1

        private const val TEST_DIR = "functions/spoof2/"
        private val TEST_CLASS_DIR = TEST_DIR + Spoof2Test::class.java.simpleName + "/"
        private const val TEST_CONF = "SystemML-config-spoof2.xml"
        private val TEST_CONF_FILE = File(SCRIPT_DIR + TEST_DIR, TEST_CONF)

        private const val eps = 10.0e-10

        @JvmStatic
        @Parameterized.Parameters(name = "{index}: testSpoof2({0}, rewrites={1}, {2})")
        fun testParams(): Collection<Array<Any>> {
            val params = ArrayList<Array<Any>>(NUM_TESTS * 3)
            for (testNum in 1..NUM_TESTS) {
                val testName = TEST_NAME + testNum
                params.add(arrayOf(testName, false, CP))
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
    fun testCodegenRowAgg() {
        testCodegenIntegration(testName, rewrites, execType)
    }


    private fun testCodegenIntegration(testname: String, rewrites: Boolean, instType: LopProperties.ExecType) {
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
            programArgs = arrayOf("-explain", "recompile_hops", "-stats", "-args", output("S"))

            fullRScriptName = HOME + testname + ".R"
            rCmd = getRCmd(inputDir(), expectedDir())

            OptimizerUtils.ALLOW_ALGEBRAIC_SIMPLIFICATION = rewrites

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
        println("This test case overrides default configuration with " + TEST_CONF_FILE.path)
        return TEST_CONF_FILE
    }


}

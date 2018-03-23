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
        private val execType: ExecType,
        private val dcs: List<DC>
) : AutomatedTestBase() {

    companion object {
        private const val TEST_NAME = "spoof2pattern"
        //	TEST_NAME+ 1;  //t(X)
        //	TEST_NAME+ 2;  //rowSum(t(X)) -- check for +C
        //	TEST_NAME+ 3;  //colSum(t(X)) -- check for +R
        //	TEST_NAME+ 4;  //sum(t(X))
        //	TEST_NAME+ 5;  //t(X%*%Y)
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
        //	TEST_NAME+21;  //X*Y*X
        //	TEST_NAME+22;  //X%*%Y%*%X;
        //	TEST_NAME+23;  //CSE
        //	TEST_NAME+24;  //sum(X%*%Y)
        //	TEST_NAME+25;  //sum( (U%*%t(V))^2 ) // need common subexpression splitting, power-to-multiply
        //	TEST_NAME+26;  //X * (r %*% M %*% c) // the right multiply results in a scalar; the sum-product block can be partitioned
        //	TEST_NAME+27;  //((X * X) %*% Y) * Z
        //	TEST_NAME+28;  //((X * X) %*% Y)
        //	TEST_NAME+29;  //((X * X^2.2) %*% Y)
        //	TEST_NAME+30;  //((X * Z) %*% Y)
        //	TEST_NAME+31;  //(A%*%B)%*%(A%*%B)
        //	TEST_NAME+32;  *//sum((X - U %*% t(V)) ^ 2)
        //	TEST_NAME+33;  //(A%*%B)*(A%*%B)
        //	TEST_NAME+34;  //rowSums(A^2)*rowSums(A)
        //	TEST_NAME+35;  //A*rowSums(A^2)
        //	TEST_NAME+36;  //rowSums(A*A)%*%colSums(A*A) // R: outer(rowSums(A*A),colSums(A))
        //	TEST_NAME+37;  //(X + U%*%t(V))^2
        //	TEST_NAME+38;  //sum( (X + X*(U%*%t(V))) ) // don't push the agg down because we can share the read of X
        //	TEST_NAME+39;  *//cbind(ABCD, t(BCDE)) // todo: check we take advantage of the CSE to get a cheaper plan
        //	TEST_NAME+40;  //A%*%A%*%A%*%A%*%A
        //	TEST_NAME+41;  //cbind(A%*%B%*%A%*%B, B%*%A%*%B%*%A)
        //	TEST_NAME+42;  //sum(A - U %*% S %*% t(V))
        //	TEST_NAME+43;  //AB, ABC, BCD, where B=log(CDE)
        //	TEST_NAME+44;  //sum(A+7) // test aggregation over an edge that does not have the aggregated name
        //	TEST_NAME+45;  //sum(A)+7
        //	TEST_NAME+46;  //sum(A)+7, with print statement
        //	TEST_NAME+47;  //AB, t(B)t(A)
        //	TEST_NAME+48;  //t(t(-2 * (X %*% t(C))) + rowSums (C ^ 2));  //genRandData4Kmeans
        //	TEST_NAME+49;  //AB + AC
        //	TEST_NAME+50;  //ABC + DBE
        //	TEST_NAME+51;  // B=B1%*%B2; (A+B) / (rowSums(A+B) %*% C)
        //	TEST_NAME+52;  //X + X * (r %*% M %*% c) // + above a partition-able problem (test case 26)
        //	TEST_NAME+53;  //AB + AC + A // we can factor A from the first two terms thanks to RewriteSplitBU_ExtendNormalForm
        //	TEST_NAME+54;  //A*B + A*C + A
        //	TEST_NAME+55;  //A*B + A + C*D + C
        //	TEST_NAME+56;  //A%*%B + A
        //	TEST_NAME+57;  //A%*%A%*%A%*%A
        //	TEST_NAME+58;  //(-X)%*%y
        //	TEST_NAME+59;  //sum(0.001 * X)
        //	TEST_NAME+60;  //rowSums(A %*% t(B))
        //	TEST_NAME+61;  //sum(A+B)
        //	TEST_NAME+62;  //(rowSums(A) %*% colSums(A)) / sum(A)
        //	TEST_NAME+63;  //A - A*B
        //	TEST_NAME+64;  //A*b*A*C*A*d
        //	TEST_NAME+65;  //t(A) %*% (B + v)
        //	TEST_NAME+66;  //t(X + colSums(X)) %*% (X + colSums(X))  // evil example...
        //	TEST_NAME+67;  //t(X) %*% (P * (X %*% V) - P * rowSums(P * (X %*% V)))
        //	TEST_NAME+68;  //t(colSums(X)) %*% (colSums(X))
        //	TEST_NAME+69;  //X + colSums(X)
        //	TEST_NAME+70;  //(X + colSums(X)) %*% Y
        //	TEST_NAME+71;  //t(X)%*%X + 2*t(colSums(X))%*%colSums(X) + 3*t(colSums(X))%*%colSums(X) // expanded form of 66
        //	TEST_NAME+72;  //C %*% S #C is a col vector; S is a scalar; no algebraic rewrites
        //	TEST_NAME+73;  //S %*% R #R is a row vector; S is a scalar; no algebraic rewrites
        //	TEST_NAME+74;  //complex from GLM.dml that stresses factoring CSEs from +
        //	TEST_NAME+75;  //y + x*(m + y) // a minus prevents the result from factoring as much as it could have otherwise. Change 0-Y to Y*(-1).
        //	TEST_NAME+76;  //A * log(3) // check correct type on log
        //	TEST_NAME+77;  //A * 3 / 4  // check correct type on div
        //	TEST_NAME+78;  //print(R), print(R^2) // check that commutative CSE elim does not comebine improperly
        //	TEST_NAME+79;  //if statement with predicate
        //	TEST_NAME+80;  //GLM snippet
        //	TEST_NAME+81;  //sum(A * (u %*% t(v) + a %*% t(y))) ==> t(u) %*% A %*% v + t(x) %*% A %*% y
                           // interesting idea: do both and test whether they are equal for particular matrices
        //	TEST_NAME+82;  //A - B - C
        //	TEST_NAME+83;  //A - B - B
        //	TEST_NAME+84;  //print ("test " + (i - 1) + " test");
        //	TEST_NAME+85;  //fragment from line 205 of mlogreg
        //	TEST_NAME+86;  //sum( U%*%t(V)%*%U )
        //	TEST_NAME+87;  //sum( (U%*%t(V))*U )
        //	TEST_NAME+88;  //(C %*% X) + rowSums (C ^ 2);
        //	TEST_NAME+89;  //(C %*% X) + rowSums (C);
        //	TEST_NAME+90;  //0 * v + v + Σ(v * 0)
        //	TEST_NAME+91;  //cbind(0 * v,v)
        //	TEST_NAME+92;  //exp(0 * v)
        //	TEST_NAME+93;  //1 * v + v + Σ(v * 1)
        //	TEST_NAME+94;  //l2svm inner loop - memory test. Modified to use max(out, 1) instead of out * (out > 0)
        //	TEST_NAME+95;  //X - colSums(X)
        //	TEST_NAME+96;  //cbind(u %*% t(v), v %*% t(u))
        private const val NUM_TESTS = 73
        private val ACTIVE_TESTS = (1..NUM_TESTS).toList() + (75..79) + (81..96)
        private val _DO_DOT: List<Pair<Int, DC>> = listOf(
//                85 to DC(arrayListOf(29, 30), performSpoofRewrites = false),
//                85 to DC(arrayListOf(29, 30))
        )
        private const val DO_R = true

        private val DO_DOT: Map<Int, List<DC>>
        init {
            DO_DOT = _DO_DOT.groupBy { it.first }.mapValues { (_,v) -> v.map { it.second } }
        }
        private const val TEST_DIR = "functions/spoof2/"
        private val TEST_CLASS_DIR = TEST_DIR + Spoof2Test::class.java.simpleName + "/"
        private const val TEST_CONF_SPOOF2 = "SystemML-config-spoof2.xml"
        private const val TEST_CONF_NOSPOOF2 = "SystemML-config-nospoof2.xml"
        private val TEST_CONF_FILE_SPOOF2 = File(SCRIPT_DIR + TEST_DIR, TEST_CONF_SPOOF2)
        private val TEST_CONF_FILE_NOSPOOF2 = File(SCRIPT_DIR + TEST_DIR, TEST_CONF_NOSPOOF2)
        private const val eps = 10.0e-10

        data class DC(
                val lines: ArrayList<Int> = arrayListOf(),
                val performHOPRewrites: Boolean = true,
                val withSubgraph: Boolean = true,
                val performSpoofRewrites: Boolean = true
        )

        @JvmStatic
        @Parameterized.Parameters(name = "{0}, rewrites={1}, {2}")
        fun testParams(): Collection<Array<Any>> {
            val params = ArrayList<Array<Any>>(NUM_TESTS * 3)
            for (testNum in ACTIVE_TESTS) {
//                if (testNum != NUM_TESTS) continue

                val testName = TEST_NAME + testNum
//                params.add(arrayOf(testName, false, CP))
//                params.add(arrayOf(testName, false, SPARK))

                val dc = DO_DOT[testNum] ?: emptyList()

                params.add(arrayOf(testName, true, CP, dc))
            }
            return params
        }
    }

    override fun setUp() {
        TestUtils.clearAssertionInformation()
        for (i in ACTIVE_TESTS)
            addTestConfiguration(TEST_NAME + i, TestConfiguration(TEST_CLASS_DIR, TEST_NAME + i, arrayOf(i.toString())))
    }

    @Test
    fun test() {
        testIt(testName, rewrites, execType, dcs)
    }


    private fun testIt(testname: String, rewrites: Boolean, instType: LopProperties.ExecType, dcs: List<DC>) {
        val platformOld = AutomatedTestBase.rtplatform
        when (instType) {
            MR -> AutomatedTestBase.rtplatform = DMLScript.RUNTIME_PLATFORM.HADOOP
            SPARK -> AutomatedTestBase.rtplatform = DMLScript.RUNTIME_PLATFORM.SPARK
            else -> AutomatedTestBase.rtplatform = DMLScript.RUNTIME_PLATFORM.HYBRID_SPARK
        }

        val sparkConfigOld = DMLScript.USE_LOCAL_SPARK_CONFIG
        if (AutomatedTestBase.rtplatform == DMLScript.RUNTIME_PLATFORM.SPARK || AutomatedTestBase.rtplatform == DMLScript.RUNTIME_PLATFORM.HYBRID_SPARK)
            DMLScript.USE_LOCAL_SPARK_CONFIG = true

        val oldAlgebraicSimplify = OptimizerUtils.ALLOW_ALGEBRAIC_SIMPLIFICATION
        if( testname in setOf(TEST_NAME+72, TEST_NAME+73) ) {
            OptimizerUtils.ALLOW_ALGEBRAIC_SIMPLIFICATION = false
        }

        try {
            val config = getTestConfiguration(testname)
            loadTestConfiguration(config)

            val HOME = AutomatedTestBase.SCRIPT_DIR + TEST_DIR
            fullDMLScriptName = HOME + testname + ".dml"
//            if ( rewrites ) // "-explain", "recompile_hops",
            programArgs = arrayOf("-stats", //"-explain", "recompile_hops",
                    "-args", output("S"))

            fullRScriptName = HOME + testname + ".R"
            rCmd = getRCmd(inputDir(), expectedDir())

            runTest(true, false, null, -1)
            dcs.forEach { dc ->
                testdml2dot(dc.lines, dc.performHOPRewrites, dc.withSubgraph, dc.performSpoofRewrites)
            }
            if( DO_R ) {
                runRScript(true)

                //compare matrices
                val dmlfile = AutomatedTestBase.readDMLMatrixFromHDFS("S")
                val rfile = readRMatrixFromFS("S")
                TestUtils.compareMatrices(dmlfile, rfile, eps, "Stat-DML", "Stat-R")
            }

            //ensure full aggregates for certain patterns
            val testnum = testname.substring(TEST_NAME.length, testname.length).toInt()
            if ("-stats" in programArgs && testnum in listOf(82, 84, 95))
                Assert.assertTrue(heavyHittersContainsSubString("-"))

        } finally {
            AutomatedTestBase.rtplatform = platformOld
            DMLScript.USE_LOCAL_SPARK_CONFIG = sparkConfigOld
            OptimizerUtils.ALLOW_ALGEBRAIC_SIMPLIFICATION = oldAlgebraicSimplify
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

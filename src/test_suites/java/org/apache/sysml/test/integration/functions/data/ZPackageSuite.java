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

package org.apache.sysml.test.integration.functions.data;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

/** Group together the tests in this package into a single suite so that the Maven build
 *  won't run two of them at once. */
@RunWith(Suite.class)
@Suite.SuiteClasses({
	FullReblockTest.class,
	FullStringInitializeTest.class,
	RandRuntimePlatformTest.class,
	RandTest1.class,
	RandTest2.class,
	RandTest3.class,
	RandTest4.class,
	RandTest5.class,
	RandVarMinMaxTest.class,
	RandVarSeedTest.class,
	ReadMMTest.class,
	ReblockTest.class,
	SampleTest.class,
	SequenceTest.class,
	VariableTest.class,
	WriteMMTest.class,
	WriteReadZeroDimsTest.class,
	WriteTest.class,
})


/** This class is just a holder for the above JUnit annotations. */
public class ZPackageSuite {

}

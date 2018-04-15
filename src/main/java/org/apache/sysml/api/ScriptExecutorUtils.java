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

package org.apache.sysml.api;

import java.util.List;

import org.apache.sysml.api.mlcontext.ScriptExecutor;
import org.apache.sysml.conf.ConfigurationManager;
import org.apache.sysml.conf.DMLConfig;
import org.apache.sysml.hops.codegen.SpoofCompiler;
import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.controlprogram.Program;
import org.apache.sysml.runtime.controlprogram.context.ExecutionContext;
import org.apache.sysml.runtime.instructions.gpu.context.GPUContext;
import org.apache.sysml.runtime.instructions.gpu.context.GPUContextPool;
import org.apache.sysml.utils.NativeHelper;
import org.apache.sysml.utils.Statistics;

public class ScriptExecutorUtils {

	/**
	 * Execute the runtime program. This involves execution of the program
	 * blocks that make up the runtime program and may involve dynamic
	 * recompilation.
	 * 
	 * @param se
	 *            script executor
	 * @param statisticsMaxHeavyHitters
	 *            maximum number of statistics to print
	 */
	public static void executeRuntimeProgram(ScriptExecutor se, int statisticsMaxHeavyHitters) {
		Program prog = se.getRuntimeProgram();
		ExecutionContext ec = se.getExecutionContext();
		DMLConfig config = se.getConfig();
		executeRuntimeProgram(prog, ec, config, statisticsMaxHeavyHitters);
	}

	/**
	 * Execute the runtime program. This involves execution of the program
	 * blocks that make up the runtime program and may involve dynamic
	 * recompilation.
	 * 
	 * @param rtprog
	 *            runtime program
	 * @param ec
	 *            execution context
	 * @param dmlconf
	 *            dml configuration
	 * @param statisticsMaxHeavyHitters
	 *            maximum number of statistics to print
	 */
	public static void executeRuntimeProgram(Program rtprog, ExecutionContext ec, DMLConfig dmlconf, int statisticsMaxHeavyHitters) {
		// Whether extra statistics useful for developers and others interested
		// in digging into performance problems are recorded and displayed
		DMLScript.FINEGRAINED_STATISTICS = DMLScript.STATISTICS && dmlconf.getBooleanValue(DMLConfig.EXTRA_FINEGRAINED_STATS);
		DMLScript.SYNCHRONIZE_GPU = dmlconf.getBooleanValue(DMLConfig.SYNCHRONIZE_GPU);
		DMLScript.EAGER_CUDA_FREE = dmlconf.getBooleanValue(DMLConfig.EAGER_CUDA_FREE);
		DMLScript.STATISTICS_MAX_WRAP_LEN = dmlconf.getIntValue(DMLConfig.STATS_MAX_WRAP_LEN);		
		NativeHelper.initialize(dmlconf.getTextValue(DMLConfig.NATIVE_BLAS_DIR), dmlconf.getTextValue(DMLConfig.NATIVE_BLAS).trim());
		
		if(DMLScript.USE_ACCELERATOR) {
			DMLScript.FLOATING_POINT_PRECISION = dmlconf.getTextValue(DMLConfig.FLOATING_POINT_PRECISION);
			org.apache.sysml.runtime.matrix.data.LibMatrixCUDA.resetFloatingPointPrecision();
		}

		boolean exceptionThrown = false;

		Statistics.startRunTimer();
		try {
			// run execute (w/ exception handling to ensure proper shutdown)
			if (DMLScript.USE_ACCELERATOR && ec != null) {
				List<GPUContext> gCtxs = GPUContextPool.reserveAllGPUContexts();
				if (gCtxs == null) {
					throw new DMLRuntimeException(
							"GPU : Could not create GPUContext, either no GPU or all GPUs currently in use");
				}
				gCtxs.get(0).initializeThread();
				ec.setGPUContexts(gCtxs);
			}
			rtprog.execute(ec);
		} catch (Throwable e) {
			exceptionThrown = true;
			throw e;
		} finally { // ensure cleanup/shutdown
			if (DMLScript.USE_ACCELERATOR && !ec.getGPUContexts().isEmpty()) {
				for(GPUContext gCtx : ec.getGPUContexts()) {
					gCtx.clearTemporaryMemory();
				}
				GPUContextPool.freeAllGPUContexts();
			}
			if( ConfigurationManager.isCodegenEnabled() )
				SpoofCompiler.cleanupCodeGenerator();
			
			// display statistics (incl caching stats if enabled)
			Statistics.stopRunTimer();
			(exceptionThrown ? System.err : System.out)
				.println(Statistics.display(statisticsMaxHeavyHitters > 0 ?
					statisticsMaxHeavyHitters : DMLScript.STATISTICS_COUNT));
		}
	}

}

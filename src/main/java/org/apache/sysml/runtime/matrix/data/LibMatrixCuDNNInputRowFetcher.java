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
package org.apache.sysml.runtime.matrix.data;

import static jcuda.runtime.JCuda.cudaMemset;
import jcuda.Pointer;
import jcuda.Sizeof;

import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.controlprogram.caching.MatrixObject;
import org.apache.sysml.runtime.instructions.gpu.GPUInstruction;
import org.apache.sysml.runtime.instructions.gpu.context.CSRPointer;
import org.apache.sysml.runtime.instructions.gpu.context.GPUContext;
import org.apache.sysml.utils.GPUStatistics;

/**
 * Performs a slice operation: out = in[(n+1):(n+1), 1:numColumns]
 */
public class LibMatrixCuDNNInputRowFetcher implements java.lang.AutoCloseable {
	GPUContext gCtx; String instName; int numColumns; boolean isInputInSparseFormat; 
	Object inPointer; // can be either CSRPointer or Pointer 
	Pointer outPointer;

	/**
	 * Initialize the input fetcher
	 * 
	 * @param gCtx current gpu context
	 * @param instName name of the instruction
	 * @param image input matrix object.
	 * @throws DMLRuntimeException if error
	 */
	public LibMatrixCuDNNInputRowFetcher(GPUContext gCtx, String instName, MatrixObject image) throws DMLRuntimeException {
		this.gCtx = gCtx; this.instName = instName;
		numColumns = LibMatrixCuDNN.toInt(image.getNumColumns());
		isInputInSparseFormat = LibMatrixCuDNN.isInSparseFormat(gCtx, image);
		inPointer = isInputInSparseFormat ? LibMatrixCuDNN.getSparsePointer(gCtx, image, instName) : LibMatrixCuDNN.getDensePointerForCuDNN(gCtx, image, instName);
		outPointer = gCtx.allocate(numColumns*Sizeof.DOUBLE);
	}
	/**
	 * Copy the nth row and return the dense pointer
	 * @param n zero-based row index
	 * @return dense pointer containing the nth row. This row is reused in the next iteration
	 * @throws DMLRuntimeException
	 */
	public Pointer getNthRow(int n) throws DMLRuntimeException {
		if(isInputInSparseFormat) {
			jcuda.runtime.JCuda.cudaDeviceSynchronize();
			long t0 = GPUStatistics.DISPLAY_STATISTICS ? System.nanoTime() : 0;
			cudaMemset(outPointer, 0, numColumns*Sizeof.DOUBLE);
			jcuda.runtime.JCuda.cudaDeviceSynchronize();
			if(GPUStatistics.DISPLAY_STATISTICS) GPUStatistics.maintainCPMiscTimes(instName, GPUInstruction.MISC_TIMER_SET_ZERO, System.nanoTime() - t0);
			LibMatrixCuDNN.sliceSparseDense(gCtx, instName, (CSRPointer)inPointer, outPointer, n, n, 0, LibMatrixCuDNN.toInt(numColumns-1), numColumns);
		}
		else {
			LibMatrixCuDNN.sliceDenseDense(gCtx, instName, (Pointer)inPointer, outPointer, n, n, 0, LibMatrixCuDNN.toInt(numColumns-1), numColumns);
		}
		return outPointer;
	}
	/**
	 * Deallocates temporary pointer
	 */
	@Override
	public void close() {
		gCtx.cudaFreeHelper(outPointer, true);
	}
}
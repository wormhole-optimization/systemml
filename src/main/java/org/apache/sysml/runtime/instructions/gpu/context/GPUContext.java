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
package org.apache.sysml.runtime.instructions.gpu.context;

import static jcuda.jcublas.JCublas2.cublasCreate;
import static jcuda.jcublas.JCublas2.cublasDestroy;
import static jcuda.jcudnn.JCudnn.cudnnCreate;
import static jcuda.jcudnn.JCudnn.cudnnDestroy;
import static jcuda.jcusolver.JCusolverDn.cusolverDnCreate;
import static jcuda.jcusolver.JCusolverDn.cusolverDnDestroy;
import static jcuda.jcusolver.JCusolverSp.cusolverSpCreate;
import static jcuda.jcusolver.JCusolverSp.cusolverSpDestroy;
import static jcuda.jcusparse.JCusparse.cusparseCreate;
import static jcuda.jcusparse.JCusparse.cusparseDestroy;
import static jcuda.runtime.JCuda.cudaDeviceScheduleBlockingSync;
import static jcuda.runtime.JCuda.cudaFree;
import static jcuda.runtime.JCuda.cudaGetDeviceCount;
import static jcuda.runtime.JCuda.cudaMalloc;
import static jcuda.runtime.JCuda.cudaMemGetInfo;
import static jcuda.runtime.JCuda.cudaMemset;
import static jcuda.runtime.JCuda.cudaSetDevice;
import static jcuda.runtime.JCuda.cudaSetDeviceFlags;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.commons.logging.Log;
import org.apache.commons.logging.LogFactory;
import org.apache.sysml.api.DMLScript;
import org.apache.sysml.conf.ConfigurationManager;
import org.apache.sysml.conf.DMLConfig;
import org.apache.sysml.hops.OptimizerUtils;
import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.controlprogram.caching.MatrixObject;
import org.apache.sysml.runtime.instructions.gpu.GPUInstruction;
import org.apache.sysml.utils.GPUStatistics;
import org.apache.sysml.utils.LRUCacheMap;

import jcuda.Pointer;
import jcuda.jcublas.cublasHandle;
import jcuda.jcudnn.cudnnHandle;
import jcuda.jcusolver.cusolverDnHandle;
import jcuda.jcusolver.cusolverSpHandle;
import jcuda.jcusparse.cusparseHandle;
import jcuda.runtime.JCuda;
import jcuda.runtime.cudaDeviceProp;

/**
 * Represents a context per GPU accessible through the same JVM.
 * Each context holds cublas, cusparse, cudnn... handles which are separate for each GPU.
 */
public class GPUContext {

	protected static final Log LOG = LogFactory.getLog(GPUContext.class.getName());
	/**
	 * currently employed eviction policy
	 */
	public final EvictionPolicy evictionPolicy = EvictionPolicy.LRU;
	/**
	 * The minimum CUDA Compute capability needed for SystemML.
	 * After compute capability 3.0, 2^31 - 1 blocks and 1024 threads per block are supported.
	 * If SystemML needs to run on an older card, this logic can be revisited.
	 */
	final int MAJOR_REQUIRED = 3;
	final int MINOR_REQUIRED = 0;
	/**
	 * active device assigned to this GPUContext instance
	 */
	private final int deviceNum;
	/**
	 * cudnnHandle for Deep Neural Network operations on the GPU
	 */
	private cudnnHandle cudnnHandle;
	/**
	 * cublasHandle for BLAS operations on the GPU
	 */
	private cublasHandle cublasHandle;
	/**
	 * cusparseHandle for certain sparse BLAS operations on the GPU
	 */
	private cusparseHandle cusparseHandle;
	/**
	 * cusolverDnHandle for invoking solve() function on dense matrices on the GPU
	 */
	private cusolverDnHandle cusolverDnHandle;
	/**
	 * cusolverSpHandle for invoking solve() function on sparse matrices on the GPU
	 */
	private cusolverSpHandle cusolverSpHandle;
	/**
	 * to launch custom CUDA kernel, specific to the active GPU for this GPUContext
	 */
	private JCudaKernels kernels;

	// Invoke cudaMemGetInfo to get available memory information. Useful if GPU is shared among multiple application.
	public double GPU_MEMORY_UTILIZATION_FACTOR = ConfigurationManager.getDMLConfig()
			.getDoubleValue(DMLConfig.GPU_MEMORY_UTILIZATION_FACTOR);
	/**
	 * Map of free blocks allocate on GPU. maps size_of_block -> pointer on GPU
	 */
	private LRUCacheMap<Long, Set<Pointer>> freeCUDASpaceMap = new LRUCacheMap<>();
	/**
	 * To record size of allocated blocks
	 */
	private HashMap<Pointer, Long> cudaBlockSizeMap = new HashMap<>();
	/**
	 * list of allocated {@link GPUObject} instances allocated on {@link GPUContext#deviceNum} GPU
	 * These are matrices allocated on the GPU on which rmvar hasn't been called yet.
	 * If a {@link GPUObject} has more than one lock on it, it cannot be freed
	 * If it has zero locks on it, it can be freed, but it is preferrable to keep it around
	 * so that an extraneous host to dev transfer can be avoided
	 */
	private ArrayList<GPUObject> allocatedGPUObjects = new ArrayList<>();

	protected GPUContext(int deviceNum) throws DMLRuntimeException {
		this.deviceNum = deviceNum;
		cudaSetDevice(deviceNum);

		cudaSetDeviceFlags(cudaDeviceScheduleBlockingSync);

		long free[] = { 0 };
		long total[] = { 0 };
		cudaMemGetInfo(free, total);

		long start = -1;
		if (DMLScript.STATISTICS)
			start = System.nanoTime();
		initializeCudaLibraryHandles();

		if (DMLScript.STATISTICS)
			GPUStatistics.cudaLibrariesInitTime = System.nanoTime() - start;

		LOG.info(" GPU memory - Total: " + (total[0] * (1e-6)) + " MB, Available: " + (free[0] * (1e-6)) + " MB on "
				+ this);

		if (GPUContextPool.initialGPUMemBudget() > OptimizerUtils.getLocalMemBudget()) {
			LOG.warn("Potential under-utilization: GPU memory (" + GPUContextPool.initialGPUMemBudget()
					+ ") > driver memory budget (" + OptimizerUtils.getLocalMemBudget() + "). "
					+ "Consider increasing the driver memory budget.");
		}
	}

	/**
	 * Returns which device is currently being used.
	 *
	 * @return the current device for the calling host thread
	 */
	public static int cudaGetDevice() {
		int[] device = new int[1];
		JCuda.cudaGetDevice(device);
		return device[0];
	}

	/**
	 * Print information of memory usage.
	 *
	 * @param opcode opcode of caller
	 * @throws DMLRuntimeException if error
	 */
	public void printMemoryInfo(String opcode) throws DMLRuntimeException {
		if (LOG.isDebugEnabled()) {
			long totalFreeCUDASpace = 0;
			for (Entry<Long, Set<Pointer>> kv : freeCUDASpaceMap.entrySet()) {
				totalFreeCUDASpace += kv.getKey() * kv.getValue().size();
			}
			long readLockedAllocatedMemory = 0;
			long writeLockedAllocatedMemory = 0;
			long unlockedAllocatedMemory = 0;
			for (GPUObject gpuObj : allocatedGPUObjects) {
				if (gpuObj.readLocks.longValue() > 0)
					readLockedAllocatedMemory += gpuObj.getSizeOnDevice();
				else if (gpuObj.writeLock)
					writeLockedAllocatedMemory += gpuObj.getSizeOnDevice();
				else
					unlockedAllocatedMemory += gpuObj.getSizeOnDevice();
			}
			long free[] = { 0 };
			long total[] = { 0 };
			cudaMemGetInfo(free, total);
			long gpuFreeMemory = (long) (free[0] * GPU_MEMORY_UTILIZATION_FACTOR);
			LOG.debug(opcode + ": Total memory: " + total[0] + ", Free memory: " + free[0] + " (with util factor: "
					+ gpuFreeMemory + "), " + "Lazy unfreed memory: " + totalFreeCUDASpace
					+ ", Locked allocated memory (read/write): " + readLockedAllocatedMemory + "/"
					+ writeLockedAllocatedMemory + ", " + " Unlocked allocated memory: " + unlockedAllocatedMemory);
		}
	}

	private void initializeCudaLibraryHandles() throws DMLRuntimeException {
		deleteCudaLibraryHandles();

		if (cudnnHandle == null) {
			cudnnHandle = new cudnnHandle();
			cudnnCreate(cudnnHandle);
		}

		if (cublasHandle == null) {
			cublasHandle = new cublasHandle();
			cublasCreate(cublasHandle);
		}
		// For cublas v2, cublasSetPointerMode tells Cublas whether to expect scalar arguments on device or on host
		// This applies to arguments like "alpha" in Dgemm, and "y" in Ddot.
		// cublasSetPointerMode(LibMatrixCUDA.cublasHandle, cublasPointerMode.CUBLAS_POINTER_MODE_DEVICE);

		if (cusparseHandle == null) {
			cusparseHandle = new cusparseHandle();
			cusparseCreate(cusparseHandle);
		}

		if (cusolverDnHandle == null) {
			cusolverDnHandle = new cusolverDnHandle();
			cusolverDnCreate(cusolverDnHandle);
		}

		if (cusolverSpHandle == null) {
			cusolverSpHandle = new cusolverSpHandle();
			cusolverSpCreate(cusolverSpHandle);
		}

		if (kernels == null) {
			kernels = new JCudaKernels();
		}
	}

	/**
	 * Returns which device is assigned to this GPUContext instance.
	 *
	 * @return active device assigned to this GPUContext instance
	 */
	public int getDeviceNum() {
		return deviceNum;
	}

	/**
	 * Sets the device for the calling thread.
	 * This method must be called after
	 * {@link org.apache.sysml.runtime.controlprogram.context.ExecutionContext#getGPUContext(int)}
	 * If in a multi-threaded environment like parfor, this method must be called when in the
	 * appropriate thread.
	 *
	 * @throws DMLRuntimeException if DMLRuntimeException occurs
	 */
	public void initializeThread() throws DMLRuntimeException {
		cudaSetDevice(deviceNum);
		initializeCudaLibraryHandles();
	}

	/**
	 * Convenience method for {@link #allocate(String, long, int)}, defaults statsCount to 1.
	 *
	 * @param size size of data (in bytes) to allocate
	 * @return jcuda pointer
	 * @throws DMLRuntimeException if DMLRuntimeException occurs
	 */
	public Pointer allocate(long size) throws DMLRuntimeException {
		return allocate(null, size, 1);
	}

	/**
	 * Convenience method for {@link #allocate(String, long, int)}, defaults statsCount to 1.
	 *
	 * @param instructionName name of instruction for which to record per instruction performance statistics, null if don't want to record
	 * @param size            size of data (in bytes) to allocate
	 * @return jcuda pointer
	 * @throws DMLRuntimeException if DMLRuntimeException occurs
	 */
	public Pointer allocate(String instructionName, long size) throws DMLRuntimeException {
		return allocate(instructionName, size, 1);
	}

	/**
	 * Allocates temporary space on the device.
	 * Does not update bookkeeping.
	 * The caller is responsible for freeing up after usage.
	 *
	 * @param instructionName name of instruction for which to record per instruction performance statistics, null if don't want to record
	 * @param size            Size of data (in bytes) to allocate
	 * @param statsCount      amount to increment the cudaAllocCount by
	 * @return jcuda Pointer
	 * @throws DMLRuntimeException if DMLRuntimeException occurs
	 */
	public Pointer allocate(String instructionName, long size, int statsCount) throws DMLRuntimeException {
		long t0 = 0, t1 = 0, end = 0;
		Pointer A;
		if (freeCUDASpaceMap.containsKey(size)) {
			if (LOG.isTraceEnabled()) {
				LOG.trace(
						"GPU : in allocate from instruction " + instructionName + ", found free block of size " + (size
								/ 1024.0) + " Kbytes from previously allocated block on " + this);
			}
			if (instructionName != null && GPUStatistics.DISPLAY_STATISTICS)
				t0 = System.nanoTime();
			Set<Pointer> freeList = freeCUDASpaceMap.get(size);

			Iterator<Pointer> it = freeList.iterator(); // at this point, freeList should have at least one element
			A = it.next();
			it.remove();

			if (freeList.isEmpty())
				freeCUDASpaceMap.remove(size);
			if (instructionName != null && GPUStatistics.DISPLAY_STATISTICS)
				GPUStatistics
						.maintainCPMiscTimes(instructionName, GPUInstruction.MISC_TIMER_REUSE, System.nanoTime() - t0);
		} else {
			if (LOG.isTraceEnabled()) {
				LOG.trace(
						"GPU : in allocate from instruction " + instructionName + ", allocating new block of size " + (
								size / 1024.0) + " Kbytes on " + this);
			}
			if (DMLScript.STATISTICS)
				t0 = System.nanoTime();
			ensureFreeSpace(instructionName, size);
			A = new Pointer();
			cudaMalloc(A, size);
			if (DMLScript.STATISTICS)
				GPUStatistics.cudaAllocTime.add(System.nanoTime() - t0);
			if (DMLScript.STATISTICS)
				GPUStatistics.cudaAllocCount.add(statsCount);
			if (instructionName != null && GPUStatistics.DISPLAY_STATISTICS)
				GPUStatistics.maintainCPMiscTimes(instructionName, GPUInstruction.MISC_TIMER_ALLOCATE,
						System.nanoTime() - t0);
		}
		// Set all elements to 0 since newly allocated space will contain garbage
		if (DMLScript.STATISTICS)
			t1 = System.nanoTime();
		if (LOG.isTraceEnabled()) {
			LOG.trace("GPU : in allocate from instruction " + instructionName + ", setting block of size " + (size
					/ 1024.0) + " Kbytes to zero on " + this);
		}
		cudaMemset(A, 0, size);
		if (DMLScript.STATISTICS)
			end = System.nanoTime();
		if (instructionName != null && GPUStatistics.DISPLAY_STATISTICS)
			GPUStatistics.maintainCPMiscTimes(instructionName, GPUInstruction.MISC_TIMER_SET_ZERO, end - t1);
		if (DMLScript.STATISTICS)
			GPUStatistics.cudaMemSet0Time.add(end - t1);
		if (DMLScript.STATISTICS)
			GPUStatistics.cudaMemSet0Count.add(1);
		cudaBlockSizeMap.put(A, size);
		return A;

	}

	/**
	 * Does lazy cudaFree calls.
	 *
	 * @param toFree {@link Pointer} instance to be freed
	 */
	public void cudaFreeHelper(final Pointer toFree) {
		cudaFreeHelper(null, toFree, DMLScript.EAGER_CUDA_FREE);
	}

	/**
	 * Does lazy/eager cudaFree calls.
	 *
	 * @param toFree {@link Pointer} instance to be freed
	 * @param eager  true if to be done eagerly
	 */
	public void cudaFreeHelper(final Pointer toFree, boolean eager) {
		cudaFreeHelper(null, toFree, eager);
	}

	/**
	 * Does lazy cudaFree calls.
	 *
	 * @param instructionName name of the instruction for which to record per instruction free time, null if do not want to record
	 * @param toFree          {@link Pointer} instance to be freed
	 */
	public void cudaFreeHelper(String instructionName, final Pointer toFree) {
		cudaFreeHelper(instructionName, toFree, DMLScript.EAGER_CUDA_FREE);
	}

	/**
	 * Does cudaFree calls, lazily.
	 *
	 * @param instructionName name of the instruction for which to record per instruction free time, null if do not want to record
	 * @param toFree          {@link Pointer} instance to be freed
	 * @param eager           true if to be done eagerly
	 */
	public void cudaFreeHelper(String instructionName, final Pointer toFree, boolean eager) {
		Pointer dummy = new Pointer();
		if (toFree == dummy) // trying to free a null pointer
			return;
		long t0 = 0;
		if (!cudaBlockSizeMap.containsKey(toFree))
			throw new RuntimeException(
					"ERROR : Internal state corrupted, cache block size map is not aware of a block it trying to free up");
		long size = cudaBlockSizeMap.get(toFree);
		if (eager) {
			if (LOG.isTraceEnabled()) {
				LOG.trace("GPU : eagerly freeing cuda memory [ " + toFree + " ] for instruction " + instructionName
						+ " on " + this);
			}
			if (DMLScript.STATISTICS)
				t0 = System.nanoTime();
			cudaFree(toFree);
			cudaBlockSizeMap.remove(toFree);
			if (DMLScript.STATISTICS)
				GPUStatistics.cudaDeAllocTime.add(System.nanoTime() - t0);
			if (DMLScript.STATISTICS)
				GPUStatistics.cudaDeAllocCount.add(1);
			if (instructionName != null && GPUStatistics.DISPLAY_STATISTICS)
				GPUStatistics.maintainCPMiscTimes(instructionName, GPUInstruction.MISC_TIMER_CUDA_FREE,
						System.nanoTime() - t0);
		} else {
			if (LOG.isTraceEnabled()) {
				LOG.trace("GPU : lazily freeing cuda memory for instruction " + instructionName + " on " + this);
			}
			Set<Pointer> freeList = freeCUDASpaceMap.get(size);
			if (freeList == null) {
				freeList = new HashSet<>();
				freeCUDASpaceMap.put(size, freeList);
			}
			if (freeList.contains(toFree))
				throw new RuntimeException("GPU : Internal state corrupted, double free");
			freeList.add(toFree);
		}
	}

	/**
	 * Thin wrapper over {@link GPUContext#evict(long)}.
	 *
	 * @param size size to check
	 * @throws DMLRuntimeException if DMLRuntimeException occurs
	 */
	void ensureFreeSpace(long size) throws DMLRuntimeException {
		ensureFreeSpace(null, size);
	}

	/**
	 * Thin wrapper over {@link GPUContext#evict(long)}.
	 *
	 * @param instructionName instructionName name of the instruction for which performance measurements are made
	 * @param size            size to check
	 * @throws DMLRuntimeException if DMLRuntimeException occurs
	 */
	void ensureFreeSpace(String instructionName, long size) throws DMLRuntimeException {
		if (size < 0)
			throw new DMLRuntimeException("The size cannot be negative:" + size);
		else if (size >= getAvailableMemory())
			evict(instructionName, size);
	}

	/**
	 * Convenience wrapper over {@link GPUContext#evict(String, long)}.
	 *
	 * @param GPUSize Desired size to be freed up on the GPU
	 * @throws DMLRuntimeException If no blocks to free up or if not enough blocks with zero locks on them.
	 */
	protected void evict(final long GPUSize) throws DMLRuntimeException {
		evict(null, GPUSize);
	}

	/**
	 * Memory on the GPU is tried to be freed up until either a chunk of needed size is freed up
	 * or it fails.
	 * First the set of reusable blocks is freed up. If that isn't enough, the set of allocated matrix
	 * blocks with zero locks on them is freed up.
	 * The process cycles through the sorted list of allocated {@link GPUObject} instances. Sorting is based on
	 * number of (read) locks that have been obtained on it (reverse order). It repeatedly frees up
	 * blocks on which there are zero locks until the required size has been freed up.
	 * // TODO: update it with hybrid policy
	 *
	 * @param instructionName name of the instruction for which performance measurements are made
	 * @param neededSize      desired size to be freed up on the GPU
	 * @throws DMLRuntimeException If no reusable memory blocks to free up or if not enough matrix blocks with zero locks on them.
	 */
	protected void evict(String instructionName, final long neededSize) throws DMLRuntimeException {
		if (LOG.isTraceEnabled()) {
			LOG.trace("GPU : evict called from " + instructionName + " for size " + neededSize + " on " + this);
		}
		GPUStatistics.cudaEvictionCount.add(1);
		// Release the set of free blocks maintained in a GPUObject.freeCUDASpaceMap
		// to free up space
		LRUCacheMap<Long, Set<Pointer>> lruCacheMap = freeCUDASpaceMap;
		while (lruCacheMap.size() > 0) {
			if (neededSize <= getAvailableMemory())
				break;
			Map.Entry<Long, Set<Pointer>> toFreeListPair = lruCacheMap.removeAndGetLRUEntry();
			Set<Pointer> toFreeList = toFreeListPair.getValue();
			Long size = toFreeListPair.getKey();

			Iterator<Pointer> it = toFreeList.iterator(); // at this point, freeList should have at least one element
			Pointer toFree = it.next();
			it.remove();

			if (toFreeList.isEmpty())
				lruCacheMap.remove(size);
			cudaFreeHelper(instructionName, toFree, true);
		}

		if (neededSize <= getAvailableMemory())
			return;

		if (allocatedGPUObjects.size() == 0) {
			throw new DMLRuntimeException(
					"There is not enough memory on device for this matrix, request (" + neededSize + ")");
		}

		Collections.sort(allocatedGPUObjects, new Comparator<GPUObject>() {
			@Override
			public int compare(GPUObject p1, GPUObject p2) {
				if (p1.isLocked() && p2.isLocked()) {
					// Both are locked, so don't sort
					return 0;
				} else if (p1.isLocked()) {
					// Put the unlocked one to RHS
					// a value less than 0 if x < y; and a value greater than 0 if x > y
					return -1;
				} else if (p2.isLocked()) {
					// Put the unlocked one to RHS
					// a value less than 0 if x < y; and a value greater than 0 if x > y
					return 1;
				} else {
					// Both are unlocked
					if (evictionPolicy == EvictionPolicy.MIN_EVICT) {
						long p1Size = 0;
						long p2Size = 0;
						try {
							p1Size = p1.getSizeOnDevice() - neededSize;
							p2Size = p2.getSizeOnDevice() - neededSize;
						} catch (DMLRuntimeException e) {
							throw new RuntimeException(e);
						}

						if (p1Size >= 0 && p2Size >= 0) {
							return Long.compare(p2Size, p1Size);
						} else {
							return Long.compare(p1Size, p2Size);
						}
					} else if (evictionPolicy == EvictionPolicy.LRU || evictionPolicy == EvictionPolicy.LFU) {
						return Long.compare(p2.timestamp.get(), p1.timestamp.get());
					} else {
						throw new RuntimeException("Unsupported eviction policy:" + evictionPolicy.name());
					}
				}
			}
		});

		while (neededSize > getAvailableMemory() && allocatedGPUObjects.size() > 0) {
			GPUObject toBeRemoved = allocatedGPUObjects.get(allocatedGPUObjects.size() - 1);
			if (toBeRemoved.isLocked()) {
				throw new DMLRuntimeException(
						"There is not enough memory on device for this matrix, request (" + neededSize
								+ "). Allocated GPU objects:" + allocatedGPUObjects.toString());
			}
			if (toBeRemoved.dirty) {
				toBeRemoved.copyFromDeviceToHost();
			}

			toBeRemoved.clearData(true);
		}
	}

	/**
	 * Whether the GPU associated with this {@link GPUContext} has recorded the usage of a certain block.
	 *
	 * @param o the block
	 * @return true if present, false otherwise
	 */
	public boolean isBlockRecorded(GPUObject o) {
		return allocatedGPUObjects.contains(o);
	}

	/**
	 * @param o {@link GPUObject} instance to record
	 * @see GPUContext#allocatedGPUObjects
	 * Records the usage of a matrix block
	 */
	public void recordBlockUsage(GPUObject o) {
		allocatedGPUObjects.add(o);
	}

	/**
	 * @param o {@link GPUObject} instance to remove from the list of allocated GPU objects
	 * @see GPUContext#allocatedGPUObjects
	 * Records that a block is not used anymore
	 */
	public void removeRecordedUsage(GPUObject o) {
		allocatedGPUObjects.removeIf(a -> a.equals(o));
	}

	/**
	 * Gets the available memory on GPU that SystemML can use.
	 *
	 * @return the available memory in bytes
	 */
	public long getAvailableMemory() {
		long free[] = { 0 };
		long total[] = { 0 };
		cudaMemGetInfo(free, total);
		return (long) (free[0] * GPU_MEMORY_UTILIZATION_FACTOR);
	}

	/**
	 * Makes sure that GPU that SystemML is trying to use has the minimum compute capability needed.
	 *
	 * @throws DMLRuntimeException if the compute capability is less than what is required
	 */
	public void ensureComputeCapability() throws DMLRuntimeException {
		int[] devices = { -1 };
		cudaGetDeviceCount(devices);
		if (devices[0] == -1) {
			throw new DMLRuntimeException("Call to cudaGetDeviceCount returned 0 devices");
		}
		boolean isComputeCapable = true;
		for (int i = 0; i < devices[0]; i++) {
			cudaDeviceProp properties = GPUContextPool.getGPUProperties(i);
			int major = properties.major;
			int minor = properties.minor;
			if (major < MAJOR_REQUIRED) {
				isComputeCapable = false;
			} else if (major == MAJOR_REQUIRED && minor < MINOR_REQUIRED) {
				isComputeCapable = false;
			}
		}
		if (!isComputeCapable) {
			throw new DMLRuntimeException(
					"One of the CUDA cards on the system has compute capability lower than " + MAJOR_REQUIRED + "."
							+ MINOR_REQUIRED);
		}
	}

	/**
	 * Instantiates a new {@link GPUObject} initialized with the given {@link org.apache.sysml.runtime.controlprogram.caching.MatrixObject MatrixObject}.
	 *
	 * @param mo a {@link org.apache.sysml.runtime.controlprogram.caching.MatrixObject MatrixObject} that represents a matrix
	 * @return a new {@link GPUObject} instance
	 */
	public GPUObject createGPUObject(MatrixObject mo) {
		return new GPUObject(this, mo);
	}

	/**
	 * Gets the device properties for the active GPU (set with cudaSetDevice()).
	 *
	 * @return the device properties
	 * @throws DMLRuntimeException ?
	 */
	public cudaDeviceProp getGPUProperties() throws DMLRuntimeException {
		return GPUContextPool.getGPUProperties(deviceNum);
	}

	/**
	 * Gets the maximum number of threads per block for "active" GPU.
	 *
	 * @return the maximum number of threads per block
	 * @throws DMLRuntimeException ?
	 */
	public int getMaxThreadsPerBlock() throws DMLRuntimeException {
		cudaDeviceProp deviceProps = getGPUProperties();
		return deviceProps.maxThreadsPerBlock;
	}

	/**
	 * Gets the maximum number of blocks supported by the active cuda device.
	 *
	 * @return the maximum number of blocks supported
	 * @throws DMLRuntimeException ?
	 */
	public int getMaxBlocks() throws DMLRuntimeException {
		cudaDeviceProp deviceProp = getGPUProperties();
		return deviceProp.maxGridSize[0];
	}

	/**
	 * Gets the shared memory per block supported by the active cuda device.
	 *
	 * @return the shared memory per block
	 * @throws DMLRuntimeException ?
	 */
	public long getMaxSharedMemory() throws DMLRuntimeException {
		cudaDeviceProp deviceProp = getGPUProperties();
		return deviceProp.sharedMemPerBlock;
	}

	/**
	 * Gets the warp size supported by the active cuda device.
	 *
	 * @return the warp size
	 * @throws DMLRuntimeException ?
	 */
	public int getWarpSize() throws DMLRuntimeException {
		cudaDeviceProp deviceProp = getGPUProperties();
		return deviceProp.warpSize;
	}

	/**
	 * Returns the cudnnHandle for Deep Neural Network operations on the GPU.
	 *
	 * @return cudnnHandle for current thread
	 */
	public cudnnHandle getCudnnHandle() {
		return cudnnHandle;
	}

	/**
	 * Returns cublasHandle for BLAS operations on the GPU.
	 *
	 * @return cublasHandle for current thread
	 */
	public cublasHandle getCublasHandle() {
		return cublasHandle;
	}

	/**
	 * Returns cusparseHandle for certain sparse BLAS operations on the GPU.
	 *
	 * @return cusparseHandle for current thread
	 */
	public cusparseHandle getCusparseHandle() {
		return cusparseHandle;
	}

	/**
	 * Returns cusolverDnHandle for invoking solve() function on dense matrices on the GPU.
	 *
	 * @return cusolverDnHandle for current thread
	 */
	public cusolverDnHandle getCusolverDnHandle() {
		return cusolverDnHandle;
	}

	/**
	 * Returns cusolverSpHandle for invoking solve() function on sparse matrices on the GPU.
	 *
	 * @return cusolverSpHandle for current thread
	 */
	public cusolverSpHandle getCusolverSpHandle() {
		return cusolverSpHandle;
	}

	/**
	 * Returns utility class used to launch custom CUDA kernel, specific to the active GPU for this GPUContext.
	 *
	 * @return {@link JCudaKernels} for current thread
	 */
	public JCudaKernels getKernels() {
		return kernels;
	}

	/**
	 * Destroys this GPUContext object.
	 *
	 * @throws DMLRuntimeException if error
	 */
	public void destroy() throws DMLRuntimeException {
		if (LOG.isTraceEnabled()) {
			LOG.trace("GPU : this context was destroyed, this = " + this.toString());
		}
		clearMemory();

		deleteCudaLibraryHandles();
	}

	/**
	 *	Deletes CUDA library handles
	 */
	private void deleteCudaLibraryHandles() {
		if (cudnnHandle != null)
			cudnnDestroy(cudnnHandle);

		if (cublasHandle != null)
			cublasDestroy(cublasHandle);

		if (cusparseHandle != null)
			cusparseDestroy(cusparseHandle);

		if (cusolverDnHandle != null)
			cusolverDnDestroy(cusolverDnHandle);

		if (cusolverSpHandle != null)
			cusolverSpDestroy(cusolverSpHandle);

		cudnnHandle = null;
		cublasHandle = null;
		cusparseHandle = null;
		cusolverDnHandle = null;
		cusolverSpHandle = null;
	}

	/**
	 * Clears all memory used by this {@link GPUContext}.
	 * Be careful to ensure that no memory is currently being used in the temporary memory before invoking this.
	 * If memory is being used between MLContext invocations, they are pointed to by a {@link GPUObject} instance
	 * which would be part of the {@link MatrixObject}. The cleanup of that {@link MatrixObject} instance will
	 * cause the memory associated with that block on the GPU to be freed up.
	 *
	 * @throws DMLRuntimeException ?
	 */
	public void clearMemory() throws DMLRuntimeException {
		clearTemporaryMemory();
		while (!allocatedGPUObjects.isEmpty()) {
			GPUObject o = allocatedGPUObjects.get(0);
			if (o.isDirty()) {
				LOG.warn("Attempted to free GPU Memory when a block[" + o
						+ "] is still on GPU memory, copying it back to host.");
				o.acquireHostRead();
			}
			o.clearData(true);
		}
		allocatedGPUObjects.clear();
	}

	/**
	 * Clears up the memory used to optimize cudaMalloc/cudaFree calls.
	 */
	public void clearTemporaryMemory() {
		// To record the cuda block sizes needed by allocatedGPUObjects, others are cleared up.
		HashMap<Pointer, Long> tmpCudaBlockSizeMap = new HashMap<>();
		for (GPUObject o : allocatedGPUObjects) {
			if (o.isDirty()) {
				if (o.isSparse()) {
					CSRPointer p = o.getSparseMatrixCudaPointer();
					if (p == null)
						throw new RuntimeException("CSRPointer is null in clearTemporaryMemory");
					if (p.rowPtr != null && cudaBlockSizeMap.containsKey(p.rowPtr)) {
						tmpCudaBlockSizeMap.put(p.rowPtr, cudaBlockSizeMap.get(p.rowPtr));
					}
					if (p.colInd != null && cudaBlockSizeMap.containsKey(p.colInd)) {
						tmpCudaBlockSizeMap.put(p.colInd, cudaBlockSizeMap.get(p.colInd));
					}
					if (p.val != null && cudaBlockSizeMap.containsKey(p.val)) {
						tmpCudaBlockSizeMap.put(p.val, cudaBlockSizeMap.get(p.val));
					}

				} else {
					Pointer p = o.getJcudaDenseMatrixPtr();
					if (p == null)
						throw new RuntimeException("Pointer is null in clearTemporaryMemory");
					tmpCudaBlockSizeMap.put(p, cudaBlockSizeMap.get(p));
				}
			}
		}

		// garbage collect all temporarily allocated spaces
		for (Set<Pointer> l : freeCUDASpaceMap.values()) {
			for (Pointer p : l) {
				cudaFreeHelper(p, true);
			}
		}
		cudaBlockSizeMap.clear();
		freeCUDASpaceMap.clear();

		// Restore only those entries for which there are still blocks on the GPU
		cudaBlockSizeMap.putAll(tmpCudaBlockSizeMap);
	}

	@Override
	public String toString() {
		return "GPUContext{" + "deviceNum=" + deviceNum + '}';
	}

	/**
	 * Eviction policies for {@link GPUContext#evict(long)}.
	 */
	public enum EvictionPolicy {
		LRU, LFU, MIN_EVICT
	}

}

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

package org.apache.sysml.hops.codegen.opt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import org.apache.commons.collections.CollectionUtils;
import org.apache.commons.lang3.ArrayUtils;
import org.apache.commons.logging.Log;
import org.apache.commons.logging.LogFactory;
import org.apache.sysml.api.DMLScript;
import org.apache.sysml.api.DMLScript.RUNTIME_PLATFORM;
import org.apache.sysml.hops.AggBinaryOp;
import org.apache.sysml.hops.AggUnaryOp;
import org.apache.sysml.hops.BinaryOp;
import org.apache.sysml.hops.Hop;
import org.apache.sysml.hops.Hop.AggOp;
import org.apache.sysml.hops.Hop.Direction;
import org.apache.sysml.hops.IndexingOp;
import org.apache.sysml.hops.LiteralOp;
import org.apache.sysml.hops.OptimizerUtils;
import org.apache.sysml.hops.ParameterizedBuiltinOp;
import org.apache.sysml.hops.ReorgOp;
import org.apache.sysml.hops.TernaryOp;
import org.apache.sysml.hops.UnaryOp;
import org.apache.sysml.hops.codegen.opt.ReachabilityGraph.SubProblem;
import org.apache.sysml.hops.codegen.template.CPlanMemoTable;
import org.apache.sysml.hops.codegen.template.CPlanMemoTable.MemoTableEntry;
import org.apache.sysml.hops.codegen.template.TemplateBase.TemplateType;
import org.apache.sysml.hops.codegen.template.TemplateOuterProduct;
import org.apache.sysml.hops.codegen.template.TemplateRow;
import org.apache.sysml.hops.codegen.template.TemplateUtils;
import org.apache.sysml.hops.rewrite.HopRewriteUtils;
import org.apache.sysml.runtime.codegen.LibSpoofPrimitives;
import org.apache.sysml.runtime.controlprogram.parfor.stat.InfrastructureAnalyzer;
import org.apache.sysml.runtime.controlprogram.parfor.util.IDSequence;
import org.apache.sysml.runtime.util.UtilFunctions;
import org.apache.sysml.utils.Statistics;

/**
 * This cost-based plan selection algorithm chooses fused operators
 * based on the DAG structure and resulting overall costs. This includes
 * holistic decisions on 
 * <ul>
 *   <li>Materialization points per consumer</li>
 *   <li>Sparsity exploitation and operator ordering</li>
 *   <li>Decisions on overlapping template types</li>
 *   <li>Decisions on multi-aggregates with shared reads</li>
 *   <li>Constraints (e.g., memory budgets and block sizes)</li>  
 * </ul>
 * 
 */
public class PlanSelectionFuseCostBasedV2 extends PlanSelection
{	
	private static final Log LOG = LogFactory.getLog(PlanSelectionFuseCostBasedV2.class.getName());
	
	//common bandwidth characteristics, with a conservative write bandwidth in order 
	//to cover result allocation, write into main memory, and potential evictions
	private static final double WRITE_BANDWIDTH = 2d*1024*1024*1024;  //2GB/s
	private static final double READ_BANDWIDTH = 32d*1024*1024*1024;  //32GB/s
	private static final double COMPUTE_BANDWIDTH = 2d*1024*1024*1024 //2GFLOPs/core
		* InfrastructureAnalyzer.getLocalParallelism();
	
	//sparsity estimate for unknown sparsity to prefer sparse-safe fusion plans
	private static final double SPARSE_SAFE_SPARSITY_EST = 0.1;
	
	//optimizer configuration
	public static boolean USE_COST_PRUNING = true;
	public static boolean USE_STRUCTURAL_PRUNING = true;
	
	private static final IDSequence COST_ID = new IDSequence();
	private static final TemplateRow ROW_TPL = new TemplateRow();
	private static final BasicPlanComparator BASE_COMPARE = new BasicPlanComparator();
	private final TypedPlanComparator _typedCompare = new TypedPlanComparator();
	
	@Override
	public void selectPlans(CPlanMemoTable memo, ArrayList<Hop> roots) 
	{
		//step 1: analyze connected partitions (nodes, roots, mat points)
		Collection<PlanPartition> parts = PlanAnalyzer.analyzePlanPartitions(memo, roots, true);
		
		//step 2: optimize individual plan partitions
		int sumMatPoints = 0;
		for( PlanPartition part : parts ) {
			//create composite templates (within the partition)
			createAndAddMultiAggPlans(memo, part.getPartition(), part.getRoots());
			
			//plan enumeration and plan selection
			selectPlans(memo, part);
			sumMatPoints += part.getMatPointsExt().length;
		}
		
		//step 3: add composite templates (across partitions)
		createAndAddMultiAggPlans(memo, roots);
		
		//take all distinct best plans
		for( Entry<Long, List<MemoTableEntry>> e : getBestPlans().entrySet() )
			memo.setDistinct(e.getKey(), e.getValue());
		
		//maintain statistics
		if( DMLScript.STATISTICS )
			Statistics.incrementCodegenEnumAll(UtilFunctions.pow(2, sumMatPoints));
	}
	
	private void selectPlans(CPlanMemoTable memo, PlanPartition part) 
	{
		//prune special case patterns and invalid plans (e.g., blocksize)
		pruneInvalidAndSpecialCasePlans(memo, part);
		
		//if no materialization points, use basic fuse-all w/ partition awareness
		if( part.getMatPointsExt() == null || part.getMatPointsExt().length==0 ) {
			for( Long hopID : part.getRoots() )
				rSelectPlansFuseAll(memo, 
					memo.getHopRefs().get(hopID), null, part.getPartition());
		}
		else {
			//obtain hop compute costs per cell once
			HashMap<Long, Double> computeCosts = new HashMap<Long, Double>();
			for( Long hopID : part.getPartition() )
				getComputeCosts(memo.getHopRefs().get(hopID), computeCosts);
			
			//prepare pruning helpers and prune memo table w/ determined mat points
			StaticCosts costs = new StaticCosts(computeCosts, getComputeCost(computeCosts, memo), 
				getReadCost(part, memo), getWriteCost(part.getRoots(), memo));
			ReachabilityGraph rgraph = USE_STRUCTURAL_PRUNING ? new ReachabilityGraph(part, memo) : null;
			if( USE_STRUCTURAL_PRUNING ) {
				part.setMatPointsExt(rgraph.getSortedSearchSpace());
				for( Long hopID : part.getPartition() )
					memo.pruneRedundant(hopID, true, part.getMatPointsExt());
			}

			//enumerate and cost plans, returns optional plan
			boolean[] bestPlan = enumPlans(memo, part, costs, rgraph, 
					part.getMatPointsExt(), 0, Double.MAX_VALUE);
			
			//prune memo table wrt best plan and select plans
			HashSet<Long> visited = new HashSet<Long>();
			for( Long hopID : part.getRoots() )
				rPruneSuboptimalPlans(memo, memo.getHopRefs().get(hopID), 
					visited, part, part.getMatPointsExt(), bestPlan);
			HashSet<Long> visited2 = new HashSet<Long>();
			for( Long hopID : part.getRoots() )
				rPruneInvalidPlans(memo, memo.getHopRefs().get(hopID), 
					visited2, part, bestPlan);
			
			for( Long hopID : part.getRoots() )
				rSelectPlansFuseAll(memo, 
					memo.getHopRefs().get(hopID), null, part.getPartition());
		}
	}
	
	/**
	 * Core plan enumeration algorithm, invoked recursively for conditionally independent
	 * subproblems. This algorithm fully explores the exponential search space of 2^m,
	 * where m is the number of interesting materialization points. We iterate over
	 * a linearized search space without every instantiating the search tree. Furthermore,
	 * in order to reduce the enumeration overhead, we apply two high-impact pruning
	 * techniques (1) pruning by evolving lower/upper cost bounds, and (2) pruning by
	 * conditional structural properties (so-called cutsets of interesting points). 
	 * 
	 * @param memo memoization table of partial fusion plans
	 * @param part connected component (partition) of partial fusion plans with all necessary meta data
	 * @param costs summary of static costs (e.g., partition reads, writes, and compute costs per operator)
	 * @param rgraph reachability graph of interesting materialization points
	 * @param matPoints sorted materialization points (defined the search space)
	 * @param off offset for recursive invocation, indicating the fixed plan part
	 * @param bestC currently known best plan costs (used of upper bound)
	 * @return optimal assignment of materialization points
	 */
	private static boolean[] enumPlans(CPlanMemoTable memo, PlanPartition part, StaticCosts costs, 
		ReachabilityGraph rgraph, InterestingPoint[] matPoints, int off, double bestC)
	{
		//scan linearized search space, w/ skips for branch and bound pruning
		//and structural pruning (where we solve conditionally independent problems)
		//bestC is monotonically non-increasing and serves as the upper bound
		long len = UtilFunctions.pow(2, matPoints.length-off);
		boolean[] bestPlan = null;
		long numEvalPlans = 0, numEvalPartPlans = 0;
		
		for( long i=0; i<len; i++ ) {
			//construct assignment
			boolean[] plan = createAssignment(matPoints.length-off, off, i);
			long pskip = 0; //skip after costing
			
			//skip plans with structural pruning
			if( USE_STRUCTURAL_PRUNING && (rgraph!=null) && rgraph.isCutSet(plan) ) {
				//compute skip (which also acts as boundary for subproblems)
				pskip = rgraph.getNumSkipPlans(plan);
				
				//start increment rgraph get subproblems
				SubProblem[] prob = rgraph.getSubproblems(plan);
				
				//solve subproblems independently and combine into best plan
				for( int j=0; j<prob.length; j++ ) {
					boolean[] bestTmp = enumPlans(memo, part, 
						costs, null, prob[j].freeMat, prob[j].offset, bestC);
					LibSpoofPrimitives.vectWrite(bestTmp, plan, prob[j].freePos);
				}
				
				//note: the overall plan costs are evaluated in full, which reused
				//the default code path; hence we postpone the skip after costing
			}
			//skip plans with branch and bound pruning (cost)
			else if( USE_COST_PRUNING ) {
				double lbC = Math.max(costs._read, costs._compute) + costs._write
					+ getMaterializationCost(part, matPoints, memo, plan);
				if( lbC >= bestC ) {
					long skip = getNumSkipPlans(plan);
					if( LOG.isTraceEnabled() )
						LOG.trace("Enum: Skip "+skip+" plans (by cost).");
					i += skip - 1;
					continue;
				}
			}
			
			//cost assignment on hops. Stop early if exceeds bestC.
			double pCBound = USE_COST_PRUNING ? bestC : Double.MAX_VALUE;
			double C = getPlanCost(memo, part, matPoints, plan, costs._computeCosts, pCBound);
			if (LOG.isTraceEnabled())
				LOG.trace("Enum: " + Arrays.toString(plan) + " -> " + C);
			numEvalPartPlans += (C==Double.POSITIVE_INFINITY) ? 1 : 0;
			numEvalPlans++;
			
			//cost comparisons
			if( bestPlan == null || C < bestC ) {
				bestC = C;
				bestPlan = plan;
				if( LOG.isTraceEnabled() )
					LOG.trace("Enum: Found new best plan.");
			}
			
			//post skipping
			i += pskip;
			if( pskip !=0 && LOG.isTraceEnabled() )
				LOG.trace("Enum: Skip "+pskip+" plans (by structure).");
		}
		
		if( DMLScript.STATISTICS ) {
			Statistics.incrementCodegenEnumAllP((rgraph!=null)?len:0);
			Statistics.incrementCodegenEnumEval(numEvalPlans);
			Statistics.incrementCodegenEnumEvalP(numEvalPartPlans);
		}
		if( LOG.isTraceEnabled() )
			LOG.trace("Enum: Optimal plan: "+Arrays.toString(bestPlan));
		
		//copy best plan w/o fixed offset plan
		return (bestPlan==null) ? new boolean[matPoints.length-off] :
			Arrays.copyOfRange(bestPlan, off, bestPlan.length);
	}
	
	private static boolean[] createAssignment(int len, int off, long pos) {
		boolean[] ret = new boolean[off+len];
		Arrays.fill(ret, 0, off, true);
		long tmp = pos;
		for( int i=0; i<len; i++ ) {
			long mask = UtilFunctions.pow(2, len-i-1);
			ret[off+i] = tmp >= mask;
			tmp %= mask;
		}
		return ret;	
	}
	
	private static long getNumSkipPlans(boolean[] plan) {
		int pos = ArrayUtils.lastIndexOf(plan, true);
		return UtilFunctions.pow(2, plan.length-pos-1);
	}
	
	private static double getMaterializationCost(PlanPartition part, InterestingPoint[] M, CPlanMemoTable memo, boolean[] plan) {
		double costs = 0;
		//currently active materialization points
		HashSet<Long> matTargets = new HashSet<>();
		for( int i=0; i<plan.length; i++ ) {
			long hopID = M[i].getToHopID();
			if( plan[i] && !matTargets.contains(hopID) ) {
				matTargets.add(hopID);
				Hop hop = memo.getHopRefs().get(hopID);
				long size = getSize(hop);
				costs += size * 8 / WRITE_BANDWIDTH + 
						size * 8 / READ_BANDWIDTH;
			}
		}
		//points with non-partition consumers
		for( Long hopID : part.getExtConsumed() )
			if( !matTargets.contains(hopID) ) {
				matTargets.add(hopID);
				Hop hop = memo.getHopRefs().get(hopID);
				costs += getSize(hop) * 8 / WRITE_BANDWIDTH;
			}
		
		return costs;
	}
	
	private static double getReadCost(PlanPartition part, CPlanMemoTable memo) {
		double costs = 0;
		//get partition input reads (at least read once)
		for( Long hopID : part.getInputs() ) {
			Hop hop = memo.getHopRefs().get(hopID);
			costs += getSize(hop) * 8 / READ_BANDWIDTH;
		}
		return costs;
	}
	
	private static double getWriteCost(Collection<Long> R, CPlanMemoTable memo) {
		double costs = 0;
		for( Long hopID : R ) {
			Hop hop = memo.getHopRefs().get(hopID);
			costs += getSize(hop) * 8 / WRITE_BANDWIDTH;
		}
		return costs;
	}
	
	private static double getComputeCost(HashMap<Long, Double> computeCosts, CPlanMemoTable memo) {
		double costs = 0;
		for( Entry<Long,Double> e : computeCosts.entrySet() ) {
			Hop mainInput = memo.getHopRefs()
				.get(e.getKey()).getInput().get(0);
			costs += getSize(mainInput) * e.getValue() / COMPUTE_BANDWIDTH;
		}
		return costs;
	}
	
	private static long getSize(Hop hop) {
		return Math.max(hop.getDim1(),1) 
			* Math.max(hop.getDim2(),1);
	}
	
	//within-partition multi-agg templates
	private static void createAndAddMultiAggPlans(CPlanMemoTable memo, HashSet<Long> partition, HashSet<Long> R)
	{
		//create index of plans that reference full aggregates to avoid circular dependencies
		HashSet<Long> refHops = new HashSet<Long>();
		for( Entry<Long, List<MemoTableEntry>> e : memo.getPlans().entrySet() )
			if( !e.getValue().isEmpty() ) {
				Hop hop = memo.getHopRefs().get(e.getKey());
				for( Hop c : hop.getInput() )
					refHops.add(c.getHopID());
			}
		
		//find all full aggregations (the fact that they are in the same partition guarantees 
		//that they also have common subexpressions, also full aggregations are by def root nodes)
		ArrayList<Long> fullAggs = new ArrayList<Long>();
		for( Long hopID : R ) {
			Hop root = memo.getHopRefs().get(hopID);
			if( !refHops.contains(hopID) && isMultiAggregateRoot(root) )
				fullAggs.add(hopID);
		}
		if( LOG.isTraceEnabled() ) {
			LOG.trace("Found within-partition ua(RC) aggregations: " +
				Arrays.toString(fullAggs.toArray(new Long[0])));
		}
		
		//construct and add multiagg template plans (w/ max 3 aggregations)
		for( int i=0; i<fullAggs.size(); i+=3 ) {
			int ito = Math.min(i+3, fullAggs.size());
			if( ito-i >= 2 ) {
				MemoTableEntry me = new MemoTableEntry(TemplateType.MAGG,
					fullAggs.get(i), fullAggs.get(i+1), ((ito-i)==3)?fullAggs.get(i+2):-1, ito-i);
				if( isValidMultiAggregate(memo, me) ) {
					for( int j=i; j<ito; j++ ) {
						memo.add(memo.getHopRefs().get(fullAggs.get(j)), me);
						if( LOG.isTraceEnabled() )
							LOG.trace("Added multiagg plan: "+fullAggs.get(j)+" "+me);
					}
				}
				else if( LOG.isTraceEnabled() ) {
					LOG.trace("Removed invalid multiagg plan: "+me);
				}
			}
		}
	}
	
	//across-partition multi-agg templates with shared reads
	private void createAndAddMultiAggPlans(CPlanMemoTable memo, ArrayList<Hop> roots)
	{
		//collect full aggregations as initial set of candidates
		HashSet<Long> fullAggs = new HashSet<Long>();
		Hop.resetVisitStatus(roots);
		for( Hop hop : roots )
			rCollectFullAggregates(hop, fullAggs);
		Hop.resetVisitStatus(roots);

		//remove operators with assigned multi-agg plans
		fullAggs.removeIf(p -> memo.contains(p, TemplateType.MAGG));
	
		//check applicability for further analysis
		if( fullAggs.size() <= 1 )
			return;
	
		if( LOG.isTraceEnabled() ) {
			LOG.trace("Found across-partition ua(RC) aggregations: " +
				Arrays.toString(fullAggs.toArray(new Long[0])));
		}
		
		//collect information for all candidates 
		//(subsumed aggregations, and inputs to fused operators) 
		List<AggregateInfo> aggInfos = new ArrayList<AggregateInfo>();
		for( Long hopID : fullAggs ) {
			Hop aggHop = memo.getHopRefs().get(hopID);
			AggregateInfo tmp = new AggregateInfo(aggHop);
			for( int i=0; i<aggHop.getInput().size(); i++ ) {
				Hop c = HopRewriteUtils.isMatrixMultiply(aggHop) && i==0 ? 
					aggHop.getInput().get(0).getInput().get(0) : aggHop.getInput().get(i);
				rExtractAggregateInfo(memo, c, tmp, TemplateType.CELL);
			}
			if( tmp._fusedInputs.isEmpty() ) {
				if( HopRewriteUtils.isMatrixMultiply(aggHop) ) {
					tmp.addFusedInput(aggHop.getInput().get(0).getInput().get(0).getHopID());
					tmp.addFusedInput(aggHop.getInput().get(1).getHopID());
				}
				else	
					tmp.addFusedInput(aggHop.getInput().get(0).getHopID());
			}
			aggInfos.add(tmp);	
		}
		
		if( LOG.isTraceEnabled() ) {
			LOG.trace("Extracted across-partition ua(RC) aggregation info: ");
			for( AggregateInfo info : aggInfos )
				LOG.trace(info);
		}
		
		//sort aggregations by num dependencies to simplify merging
		//clusters of aggregations with parallel dependencies
		aggInfos = aggInfos.stream()
			.sorted(Comparator.comparing(a -> a._inputAggs.size()))
			.collect(Collectors.toList());
		
		//greedy grouping of multi-agg candidates
		boolean converged = false;
		while( !converged ) {
			AggregateInfo merged = null;
			for( int i=0; i<aggInfos.size(); i++ ) {
				AggregateInfo current = aggInfos.get(i);
				for( int j=i+1; j<aggInfos.size(); j++ ) {
					AggregateInfo that = aggInfos.get(j);
					if( current.isMergable(that) ) {
						merged = current.merge(that);
						aggInfos.remove(j); j--;
					}
				}
			}
			converged = (merged == null);
		}
		
		if( LOG.isTraceEnabled() ) {
			LOG.trace("Merged across-partition ua(RC) aggregation info: ");
			for( AggregateInfo info : aggInfos )
				LOG.trace(info);
		}
		
		//construct and add multiagg template plans (w/ max 3 aggregations)
		for( AggregateInfo info : aggInfos ) {
			if( info._aggregates.size()<=1 )
				continue;
			Long[] aggs = info._aggregates.keySet().toArray(new Long[0]);
			MemoTableEntry me = new MemoTableEntry(TemplateType.MAGG,
				aggs[0], aggs[1], (aggs.length>2)?aggs[2]:-1, aggs.length);
			for( int i=0; i<aggs.length; i++ ) {
				memo.add(memo.getHopRefs().get(aggs[i]), me);
				addBestPlan(aggs[i], me);
				if( LOG.isTraceEnabled() )
					LOG.trace("Added multiagg* plan: "+aggs[i]+" "+me);
				
			}
		}
	}
	
	private static boolean isMultiAggregateRoot(Hop root) {
		return (HopRewriteUtils.isAggUnaryOp(root, AggOp.SUM, AggOp.SUM_SQ, AggOp.MIN, AggOp.MAX) 
				&& ((AggUnaryOp)root).getDirection()==Direction.RowCol)
			|| (root instanceof AggBinaryOp && root.getDim1()==1 && root.getDim2()==1
				&& HopRewriteUtils.isTransposeOperation(root.getInput().get(0)));
	}
	
	private static boolean isValidMultiAggregate(CPlanMemoTable memo, MemoTableEntry me) {
		//ensure input consistent sizes (otherwise potential for incorrect results)
		boolean ret = true;
		Hop refSize = memo.getHopRefs().get(me.input1).getInput().get(0);
		for( int i=1; ret && i<3; i++ ) {
			if( me.isPlanRef(i) )
				ret &= HopRewriteUtils.isEqualSize(refSize, 
					memo.getHopRefs().get(me.input(i)).getInput().get(0));
		}
		
		//ensure that aggregates are independent of each other, i.e.,
		//they to not have potentially transitive parent child references
		for( int i=0; ret && i<3; i++ ) 
			if( me.isPlanRef(i) ) {
				HashSet<Long> probe = new HashSet<Long>();
				for( int j=0; j<3; j++ )
					if( i != j )
						probe.add(me.input(j));
				ret &= rCheckMultiAggregate(memo.getHopRefs().get(me.input(i)), probe);
			}
		return ret;
	}
	
	private static boolean rCheckMultiAggregate(Hop current, HashSet<Long> probe) {
		boolean ret = true;
		for( Hop c : current.getInput() )
			ret &= rCheckMultiAggregate(c, probe);
		ret &= !probe.contains(current.getHopID());
		return ret;
	}
	
	private static void rCollectFullAggregates(Hop current, HashSet<Long> aggs) {
		if( current.isVisited() )
			return;
		
		//collect all applicable full aggregations per read
		if( isMultiAggregateRoot(current) )
			aggs.add(current.getHopID());
		
		//recursively process children
		for( Hop c : current.getInput() )
			rCollectFullAggregates(c, aggs);
		
		current.setVisited();
	}
	
	private static void rExtractAggregateInfo(CPlanMemoTable memo, Hop current, AggregateInfo aggInfo, TemplateType type) {
		//collect input aggregates (dependents)
		if( isMultiAggregateRoot(current) )
			aggInfo.addInputAggregate(current.getHopID());
		
		//recursively process children
		MemoTableEntry me = (type!=null) ? memo.getBest(current.getHopID()) : null;
		for( int i=0; i<current.getInput().size(); i++ ) {
			Hop c = current.getInput().get(i);
			if( me != null && me.isPlanRef(i) )
				rExtractAggregateInfo(memo, c, aggInfo, type);
			else {
				if( type != null && c.getDataType().isMatrix()  ) //add fused input
					aggInfo.addFusedInput(c.getHopID());
				rExtractAggregateInfo(memo, c, aggInfo, null);
			}
		}
	}
	
	private static boolean isRowTemplateWithoutAgg(CPlanMemoTable memo, Hop current, HashSet<Long> visited) {
		//consider all aggregations other than root operation
		MemoTableEntry me = memo.getBest(current.getHopID(), TemplateType.ROW);
		boolean ret = true;
		for(int i=0; i<3; i++)
			if( me.isPlanRef(i) )
				ret &= rIsRowTemplateWithoutAgg(memo, 
					current.getInput().get(i), visited);
		return ret;
	}
	
	private static boolean rIsRowTemplateWithoutAgg(CPlanMemoTable memo, Hop current, HashSet<Long> visited) {
		if( visited.contains(current.getHopID()) )
			return true;
		
		boolean ret = true;
		MemoTableEntry me = memo.getBest(current.getHopID(), TemplateType.ROW);
		for(int i=0; i<3; i++)
			if( me!=null && me.isPlanRef(i) )
				ret &= rIsRowTemplateWithoutAgg(memo, current.getInput().get(i), visited);
		ret &= !(current instanceof AggUnaryOp || current instanceof AggBinaryOp);
		
		visited.add(current.getHopID());
		return ret;
	}
	
	private static void pruneInvalidAndSpecialCasePlans(CPlanMemoTable memo, PlanPartition part) 
	{	
		//prune invalid row entries w/ violated blocksize constraint
		if( OptimizerUtils.isSparkExecutionMode() ) {
			for( Long hopID : part.getPartition() ) {
				if( !memo.contains(hopID, TemplateType.ROW) )
					continue;
				Hop hop = memo.getHopRefs().get(hopID);
				boolean isSpark = DMLScript.rtplatform == RUNTIME_PLATFORM.SPARK
					|| OptimizerUtils.getTotalMemEstimate(hop.getInput().toArray(new Hop[0]), hop)
						> OptimizerUtils.getLocalMemBudget();
				boolean validNcol = true;
				for( Hop in : hop.getInput() )
					validNcol &= in.getDataType().isScalar()
						|| (in.getDim2() <= in.getColsInBlock())
						|| (hop instanceof AggBinaryOp && in.getDim1() <= in.getRowsInBlock()
						&& HopRewriteUtils.isTransposeOperation(in));
				if( isSpark && !validNcol ) {
					List<MemoTableEntry> blacklist = memo.get(hopID, TemplateType.ROW);
					memo.remove(memo.getHopRefs().get(hopID), new HashSet<MemoTableEntry>(blacklist));
					if( !memo.contains(hopID) )
						memo.removeAllRefTo(hopID);
					if( LOG.isTraceEnabled() ) {
						LOG.trace("Removed row memo table entries w/ violated blocksize constraint ("+hopID+"): "
							+ Arrays.toString(blacklist.toArray(new MemoTableEntry[0])));
					}
				}
			}
		}
		
		//prune row aggregates with pure cellwise operations
		for( Long hopID : part.getPartition() ) {
			MemoTableEntry me = memo.getBest(hopID, TemplateType.ROW);
			if( me != null && me.type == TemplateType.ROW && memo.contains(hopID, TemplateType.CELL)
				&& isRowTemplateWithoutAgg(memo, memo.getHopRefs().get(hopID), new HashSet<Long>())) {
				List<MemoTableEntry> blacklist = memo.get(hopID, TemplateType.ROW); 
				memo.remove(memo.getHopRefs().get(hopID), new HashSet<MemoTableEntry>(blacklist));
				if( LOG.isTraceEnabled() ) {
					LOG.trace("Removed row memo table entries w/o aggregation: "
						+ Arrays.toString(blacklist.toArray(new MemoTableEntry[0])));
				}
			}
		}
		
		//prune suboptimal outer product plans that are dominated by outer product plans w/ same number of 
		//references but better fusion properties (e.g., for the patterns Y=X*(U%*%t(V)) and sum(Y*(U2%*%t(V2))), 
		//we'd prune sum(X*(U%*%t(V))*Z), Z=U2%*%t(V2) because this would unnecessarily destroy a fusion pattern.
		for( Long hopID : part.getPartition() ) {
			if( memo.countEntries(hopID, TemplateType.OUTER) == 2 ) {
				List<MemoTableEntry> entries = memo.get(hopID, TemplateType.OUTER);
				MemoTableEntry me1 = entries.get(0);
				MemoTableEntry me2 = entries.get(1);
				MemoTableEntry rmEntry = TemplateOuterProduct.dropAlternativePlan(memo, me1, me2);
				if( rmEntry != null ) {
					memo.remove(memo.getHopRefs().get(hopID), Collections.singleton(rmEntry));
					memo.getPlansBlacklisted().remove(rmEntry.input(rmEntry.getPlanRefIndex()));
					if( LOG.isTraceEnabled() )
						LOG.trace("Removed dominated outer product memo table entry: " + rmEntry);
				}
			}
		}
	}
	
	private static void rPruneSuboptimalPlans(CPlanMemoTable memo, Hop current, HashSet<Long> visited, 
		PlanPartition part, InterestingPoint[] matPoints, boolean[] plan) 
	{
		//memoization (not via hops because in middle of dag)
		if( visited.contains(current.getHopID()) )
			return;
		
		//remove memo table entries if necessary
		long hopID = current.getHopID();
		if( part.getPartition().contains(hopID) && memo.contains(hopID) ) {
			Iterator<MemoTableEntry> iter = memo.get(hopID).iterator();
			while( iter.hasNext() ) {
				MemoTableEntry me = iter.next();
				if( !hasNoRefToMatPoint(hopID, me, matPoints, plan) && me.type!=TemplateType.OUTER ) {
					iter.remove();
					if( LOG.isTraceEnabled() )
						LOG.trace("Removed memo table entry: "+me);
				}
			}
		}
		
		//process children recursively
		for( Hop c : current.getInput() )
			rPruneSuboptimalPlans(memo, c, visited, part, matPoints, plan);
		
		visited.add(current.getHopID());
	}
	
	private static void rPruneInvalidPlans(CPlanMemoTable memo, Hop current, HashSet<Long> visited, PlanPartition part, boolean[] plan) {
		//memoization (not via hops because in middle of dag)
		if( visited.contains(current.getHopID()) )
			return;
		
		//process children recursively
		for( Hop c : current.getInput() )
			rPruneInvalidPlans(memo, c, visited, part, plan);
		
		//find invalid row aggregate leaf nodes (see TemplateRow.open) w/o matrix inputs, 
		//i.e., plans that become invalid after the previous pruning step
		long hopID = current.getHopID();
		if( part.getPartition().contains(hopID) && memo.contains(hopID, TemplateType.ROW) ) {
			for( MemoTableEntry me : memo.get(hopID) ) {
				if( me.type==TemplateType.ROW ) {
					//convert leaf node with pure vector inputs
					if( !me.hasPlanRef() && !TemplateUtils.hasMatrixInput(current) ) {
						me.type = TemplateType.CELL;
						if( LOG.isTraceEnabled() )
							LOG.trace("Converted leaf memo table entry from row to cell: "+me);
					}
					
					//convert inner node without row template input
					if( me.hasPlanRef() && !ROW_TPL.open(current) ) {
						boolean hasRowInput = false;
						for( int i=0; i<3; i++ )
							if( me.isPlanRef(i) )
								hasRowInput |= memo.contains(me.input(i), TemplateType.ROW);
						if( !hasRowInput ) {
							me.type = TemplateType.CELL;
							if( LOG.isTraceEnabled() )
								LOG.trace("Converted inner memo table entry from row to cell: "+me);	
						}
					}
					
				}
			}
		}
		
		visited.add(current.getHopID());		
	}
	
	private void rSelectPlansFuseAll(CPlanMemoTable memo, Hop current, TemplateType currentType, HashSet<Long> partition) 
	{	
		if( isVisited(current.getHopID(), currentType) 
			|| !partition.contains(current.getHopID()) )
			return;
		
		//step 1: prune subsumed plans of same type
		if( memo.contains(current.getHopID()) ) {
			HashSet<MemoTableEntry> rmSet = new HashSet<MemoTableEntry>();
			List<MemoTableEntry> hopP = memo.get(current.getHopID());
			for( MemoTableEntry e1 : hopP )
				for( MemoTableEntry e2 : hopP )
					if( e1 != e2 && e1.subsumes(e2) )
						rmSet.add(e2);
			memo.remove(current, rmSet);
		}
		
		//step 2: select plan for current path
		MemoTableEntry best = null;
		if( memo.contains(current.getHopID()) ) {
			if( currentType == null ) {
				best = memo.get(current.getHopID()).stream()
					.filter(p -> isValid(p, current))
					.min(BASE_COMPARE).orElse(null);
			}
			else {
				_typedCompare.setType(currentType);
				best = memo.get(current.getHopID()).stream()
					.filter(p -> p.type==currentType || p.type==TemplateType.CELL)
					.min(_typedCompare).orElse(null);
			}
			addBestPlan(current.getHopID(), best);
		}
		
		//step 3: recursively process children
		for( int i=0; i< current.getInput().size(); i++ ) {
			TemplateType pref = (best!=null && best.isPlanRef(i))? best.type : null;
			rSelectPlansFuseAll(memo, current.getInput().get(i), pref, partition);
		}
		
		setVisited(current.getHopID(), currentType);
	}
	
	/////////////////////////////////////////////////////////
	// Cost model fused operators w/ materialization points
	//////////
	
	private static double getPlanCost(CPlanMemoTable memo, PlanPartition part, 
			InterestingPoint[] matPoints,boolean[] plan, HashMap<Long, Double> computeCosts,
			final double costBound)
	{
		//high level heuristic: every hop or fused operator has the following cost: 
		//WRITE + max(COMPUTE, READ), where WRITE costs are given by the output size, 
		//READ costs by the input sizes, and COMPUTE by operation specific FLOP
		//counts times number of cells of main input, disregarding sparsity for now.
		
		HashSet<VisitMarkCost> visited = new HashSet<>();
		double costs = 0;
		int rem = part.getRoots().size();
		for( Long hopID : part.getRoots() ) {
			costs += rGetPlanCosts(memo, memo.getHopRefs().get(hopID), 
				visited, part, matPoints, plan, computeCosts, null, null, costBound-costs);
			if( costs >= costBound && --rem > 0 ) //stop early
				return Double.POSITIVE_INFINITY;
		}
		return costs;
	}
	
	private static double rGetPlanCosts(CPlanMemoTable memo, final Hop current, HashSet<VisitMarkCost> visited,
			PlanPartition part, InterestingPoint[] matPoints, boolean[] plan, HashMap<Long, Double> computeCosts,
			CostVector costsCurrent, TemplateType currentType, final double costBound)
	{
		final long currentHopId = current.getHopID();
		//memoization per hop id and cost vector to account for redundant
		//computation without double counting materialized results or compute
		//costs of complex operation DAGs within a single fused operator
		if( !visited.add(new VisitMarkCost(currentHopId, 
			(costsCurrent==null || currentType==TemplateType.MAGG)?0:costsCurrent.ID)) )
			return 0; //already existing 
		
		//open template if necessary, including memoization
		//under awareness of current plan choice
		MemoTableEntry best = null;
		boolean opened = (currentType == null);
		if( memo.contains(currentHopId) ) {
			//note: this is the inner loop of plan enumeration and hence, we do not 
			//use streams, lambda expressions, etc to avoid unnecessary overhead
			if( currentType == null ) {
				for( MemoTableEntry me : memo.get(currentHopId) )
					best = isValid(me, current) 
						&& hasNoRefToMatPoint(currentHopId, me, matPoints, plan)
						&& BasicPlanComparator.icompare(me, best)<0 ? me : best;
				opened = true;
			}
			else {
				for( MemoTableEntry me : memo.get(currentHopId) )
					best = (me.type == currentType || me.type==TemplateType.CELL)
						&& hasNoRefToMatPoint(currentHopId, me, matPoints, plan)
						&& TypedPlanComparator.icompare(me, best, currentType)<0 ? me : best;
			}
		}
		
		//create new cost vector if opened, initialized with write costs
		CostVector costVect = !opened ? costsCurrent : new CostVector(getSize(current));
		double costs = 0;
		
		//add other roots for multi-agg template to account for shared costs
		if( opened && best != null && best.type == TemplateType.MAGG ) {
			//account costs to first multi-agg root 
			if( best.input1 == currentHopId )
				for( int i=1; i<3; i++ ) {
					if( !best.isPlanRef(i) ) continue;
					costs += rGetPlanCosts(memo, memo.getHopRefs().get(best.input(i)), visited, 
						part, matPoints, plan, computeCosts, costVect, TemplateType.MAGG, costBound-costs);
					if( costs >= costBound )
						return Double.POSITIVE_INFINITY;
				}
			//skip other multi-agg roots
			else
				return 0;
		}
		
		//add compute costs of current operator to costs vector
		costVect.computeCosts += computeCosts.get(currentHopId);
		
		//process children recursively
		for( int i=0; i< current.getInput().size(); i++ ) {
			Hop c = current.getInput().get(i);
			if( best!=null && best.isPlanRef(i) )
				costs += rGetPlanCosts(memo, c, visited, part, matPoints,
						plan, computeCosts, costVect, best.type, costBound-costs);
			else if( best!=null && isImplicitlyFused(current, i, best.type) )
				costVect.addInputSize(c.getInput().get(0).getHopID(), getSize(c));
			else { //include children and I/O costs
				if( part.getPartition().contains(c.getHopID()) )
					costs += rGetPlanCosts(memo, c, visited, part, matPoints,
						plan, computeCosts, null, null, costBound-costs);
				if( costVect != null && c.getDataType().isMatrix() )
					costVect.addInputSize(c.getHopID(), getSize(c));
			}
			if( costs >= costBound )
				return Double.POSITIVE_INFINITY;
		}
		
		//add costs for opened fused operator
		if( opened ) {
			if( LOG.isTraceEnabled() ) {
				String type = (best !=null) ? best.type.name() : "HOP";
				LOG.trace("Cost vector ("+type+" "+currentHopId+"): "+costVect);
			}
			double tmpCosts = costVect.outSize * 8 / WRITE_BANDWIDTH //time for output write
				+ Math.max(costVect.getSumInputSizes() * 8 / READ_BANDWIDTH,
				costVect.computeCosts*costVect.getMaxInputSize()/ COMPUTE_BANDWIDTH);
			//sparsity correction for outer-product template (and sparse-safe cell)
			if( best != null && best.type == TemplateType.OUTER ) {
				Hop driver = memo.getHopRefs().get(costVect.getMaxInputSizeHopID());
				tmpCosts *= driver.dimsKnown(true) ? driver.getSparsity() : SPARSE_SAFE_SPARSITY_EST;
			}
			costs += tmpCosts;
		}
		//add costs for non-partition read in the middle of fused operator
		else if( part.getExtConsumed().contains(current.getHopID()) ) {
			costs += rGetPlanCosts(memo, current, visited, part, matPoints, plan,
				computeCosts, null, null, costBound - costs);
		}
		
		//sanity check non-negative costs
		if( costs < 0 || Double.isNaN(costs) || Double.isInfinite(costs) )
			throw new RuntimeException("Wrong cost estimate: "+costs);
		
		return costs;
	}
	
	private static void getComputeCosts(Hop current, HashMap<Long, Double> computeCosts) 
	{
		//get costs for given hop
		double costs = 1;
		if( current instanceof UnaryOp ) {
			switch( ((UnaryOp)current).getOp() ) {
				case ABS:   
				case ROUND:
				case CEIL:
				case FLOOR:
				case SIGN:
				case SELP:    costs = 1; break; 
				case SPROP:
				case SQRT:    costs = 2; break;
				case EXP:     costs = 18; break;
				case SIGMOID: costs = 21; break;
				case LOG:    
				case LOG_NZ:  costs = 32; break;
				case NCOL:
				case NROW:
				case PRINT:
				case CAST_AS_BOOLEAN:
				case CAST_AS_DOUBLE:
				case CAST_AS_INT:
				case CAST_AS_MATRIX:
				case CAST_AS_SCALAR: costs = 1; break;
				case SIN:     costs = 18; break;
				case COS:     costs = 22; break;
				case TAN:     costs = 42; break;
				case ASIN:    costs = 93; break;
				case ACOS:    costs = 103; break;
				case ATAN:    costs = 40; break;
				case CUMSUM:
				case CUMMIN:
				case CUMMAX:
				case CUMPROD: costs = 1; break;
				default:
					LOG.warn("Cost model not "
						+ "implemented yet for: "+((UnaryOp)current).getOp());
			}
		}
		else if( current instanceof BinaryOp ) {
			switch( ((BinaryOp)current).getOp() ) {
				case MULT: 
				case PLUS:
				case MINUS:
				case MIN:
				case MAX: 
				case AND:
				case OR:
				case EQUAL:
				case NOTEQUAL:
				case LESS:
				case LESSEQUAL:
				case GREATER:
				case GREATEREQUAL: 
				case CBIND:
				case RBIND:   costs = 1; break;
				case INTDIV:  costs = 6; break;
				case MODULUS: costs = 8; break;
				case DIV:     costs = 22; break;
				case LOG:
				case LOG_NZ:  costs = 32; break;
				case POW:     costs = (HopRewriteUtils.isLiteralOfValue(
						current.getInput().get(1), 2) ? 1 : 16); break;
				case MINUS_NZ:
				case MINUS1_MULT: costs = 2; break;
				case CENTRALMOMENT:
					int type = (int) (current.getInput().get(1) instanceof LiteralOp ? 
						HopRewriteUtils.getIntValueSafe((LiteralOp)current.getInput().get(1)) : 2);
					switch( type ) {
						case 0: costs = 1; break; //count
						case 1: costs = 8; break; //mean
						case 2: costs = 16; break; //cm2
						case 3: costs = 31; break; //cm3
						case 4: costs = 51; break; //cm4
						case 5: costs = 16; break; //variance
					}
					break;
				case COVARIANCE: costs = 23; break;
				default:
					LOG.warn("Cost model not "
						+ "implemented yet for: "+((BinaryOp)current).getOp());
			}
		}
		else if( current instanceof TernaryOp ) {
			switch( ((TernaryOp)current).getOp() ) {
				case PLUS_MULT: 
				case MINUS_MULT: costs = 2; break;
				case CTABLE:     costs = 3; break;
				case CENTRALMOMENT:
					int type = (int) (current.getInput().get(1) instanceof LiteralOp ? 
						HopRewriteUtils.getIntValueSafe((LiteralOp)current.getInput().get(1)) : 2);
					switch( type ) {
						case 0: costs = 2; break; //count
						case 1: costs = 9; break; //mean
						case 2: costs = 17; break; //cm2
						case 3: costs = 32; break; //cm3
						case 4: costs = 52; break; //cm4
						case 5: costs = 17; break; //variance
					}
					break;
				case COVARIANCE: costs = 23; break;
				default:
					LOG.warn("Cost model not "
						+ "implemented yet for: "+((TernaryOp)current).getOp());
			}
		}
		else if( current instanceof ParameterizedBuiltinOp ) {
			costs = 1;
		}
		else if( current instanceof IndexingOp ) {
			costs = 1;
		}
		else if( current instanceof ReorgOp ) {
			costs = 1;
		}
		else if( current instanceof AggBinaryOp ) {
			//outer product template
			if( HopRewriteUtils.isOuterProductLikeMM(current) )
				costs = 2 * current.getInput().get(0).getDim2();
			//row template w/ matrix-vector or matrix-matrix
			else
				costs = 2 * current .getDim2();
		}
		else if( current instanceof AggUnaryOp) {
			switch(((AggUnaryOp)current).getOp()) {
			case SUM:    costs = 4; break; 
			case SUM_SQ: costs = 5; break;
			case MIN:
			case MAX:    costs = 1; break;
			default:
				LOG.warn("Cost model not "
					+ "implemented yet for: "+((AggUnaryOp)current).getOp());			
			}
		}
		
		computeCosts.put(current.getHopID(), costs);
	}
	
	private static boolean hasNoRefToMatPoint(long hopID, 
			MemoTableEntry me, InterestingPoint[] M, boolean[] plan) {
		return !InterestingPoint.isMatPoint(M, hopID, me, plan);
	}
	
	private static boolean isImplicitlyFused(Hop hop, int index, TemplateType type) {
		return type == TemplateType.ROW
			&& HopRewriteUtils.isMatrixMultiply(hop) && index==0 
			&& HopRewriteUtils.isTransposeOperation(hop.getInput().get(index)); 
	}
	
	private static class CostVector {
		public final long ID;
		public final double outSize; 
		public double computeCosts = 0;
		public final HashMap<Long, Double> inSizes = new HashMap<Long, Double>();
		
		public CostVector(double outputSize) {
			ID = COST_ID.getNextID();
			outSize = outputSize;
		}
		public void addInputSize(long hopID, double inputSize) {
			//ensures that input sizes are not double counted
			inSizes.put(hopID, inputSize);
		}
		public double getSumInputSizes() {
			return inSizes.values().stream()
				.mapToDouble(d -> d.doubleValue()).sum();
		}
		public double getMaxInputSize() {
			return inSizes.values().stream()
				.mapToDouble(d -> d.doubleValue()).max().orElse(0);
		}
		public long getMaxInputSizeHopID() {
			long id = -1; double max = 0;
			for( Entry<Long,Double> e : inSizes.entrySet() )
				if( max < e.getValue() ) {
					id = e.getKey();
					max = e.getValue();
				}
			return id;
		}
		@Override
		public String toString() {
			return "["+outSize+", "+computeCosts+", {"
				+Arrays.toString(inSizes.keySet().toArray(new Long[0]))+", "
				+Arrays.toString(inSizes.values().toArray(new Double[0]))+"}]";
		}
	}
	
	private static class StaticCosts {
		public final HashMap<Long, Double> _computeCosts;
		public final double _compute;
		public final double _read;
		public final double _write;
		
		public StaticCosts(HashMap<Long,Double> allComputeCosts, double computeCost, double readCost, double writeCost) {
			_computeCosts = allComputeCosts;
			_compute = computeCost;
			_read = readCost;
			_write = writeCost;
		}
	}
	
	private static class AggregateInfo {
		public final HashMap<Long,Hop> _aggregates;
		public final HashSet<Long> _inputAggs = new HashSet<Long>();
		public final HashSet<Long> _fusedInputs = new HashSet<Long>();
		public AggregateInfo(Hop aggregate) {
			_aggregates = new HashMap<Long, Hop>();
			_aggregates.put(aggregate.getHopID(), aggregate);
		}
		public void addInputAggregate(long hopID) {
			_inputAggs.add(hopID);
		}
		public void addFusedInput(long hopID) {
			_fusedInputs.add(hopID);
		}
		public boolean isMergable(AggregateInfo that) {
			//check independence
			boolean ret = _aggregates.size()<3 
				&& _aggregates.size()+that._aggregates.size()<=3;
			for( Long hopID : that._aggregates.keySet() )
				ret &= !_inputAggs.contains(hopID);
			for( Long hopID : _aggregates.keySet() )
				ret &= !that._inputAggs.contains(hopID);
			//check partial shared reads
			ret &= !CollectionUtils.intersection(
				_fusedInputs, that._fusedInputs).isEmpty();
			//check consistent sizes (result correctness)
			Hop in1 = _aggregates.values().iterator().next();
			Hop in2 = that._aggregates.values().iterator().next();
			return ret && HopRewriteUtils.isEqualSize(
				in1.getInput().get(HopRewriteUtils.isMatrixMultiply(in1)?1:0),
				in2.getInput().get(HopRewriteUtils.isMatrixMultiply(in2)?1:0));
		}
		public AggregateInfo merge(AggregateInfo that) {
			_aggregates.putAll(that._aggregates);
			_inputAggs.addAll(that._inputAggs);
			_fusedInputs.addAll(that._fusedInputs);
			return this;
		}
		@Override
		public String toString() {
			return "["+Arrays.toString(_aggregates.keySet().toArray(new Long[0]))+": "
				+"{"+Arrays.toString(_inputAggs.toArray(new Long[0]))+"}," 
				+"{"+Arrays.toString(_fusedInputs.toArray(new Long[0]))+"}]"; 
		}
	}
}

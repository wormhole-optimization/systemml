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

package org.apache.sysml.hops.globalopt.gdfgraph;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.sysml.hops.DataOp;
import org.apache.sysml.hops.Hop;
import org.apache.sysml.hops.Hop.DataOpTypes;
import org.apache.sysml.hops.globalopt.Summary;
import org.apache.sysml.hops.HopsException;
import org.apache.sysml.parser.ForStatementBlock;
import org.apache.sysml.parser.IfStatementBlock;
import org.apache.sysml.parser.StatementBlock;
import org.apache.sysml.parser.WhileStatementBlock;
import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.controlprogram.ForProgramBlock;
import org.apache.sysml.runtime.controlprogram.FunctionProgramBlock;
import org.apache.sysml.runtime.controlprogram.IfProgramBlock;
import org.apache.sysml.runtime.controlprogram.Program;
import org.apache.sysml.runtime.controlprogram.ProgramBlock;
import org.apache.sysml.runtime.controlprogram.WhileProgramBlock;
import org.apache.sysml.runtime.controlprogram.parfor.stat.Timing;
import org.apache.sysml.utils.Explain;

/**
 * GENERAL 'GDF GRAPH' STRUCTURE, by MB:
 *  1) Each hop is represented by an GDFNode
 *  2) Each loop is represented by a structured GDFLoopNode
 *  3) Transient Read/Write connections are represented via CrossBlockNodes,
 *     a) type PLAIN: single input crossblocknode represents unconditional data flow
 *     b) type MERGE: two inputs crossblocknode represent conditional data flow merge
 * 
 *  In detail, the graph builder essentially does a single pass over the entire program
 *  and constructs the global data flow graph bottom up. We create crossblocknodes for
 *  every transient write, loop nodes for for/while programblocks, and crossblocknodes
 *  after every if programblock. 
 *  
 */
public class GraphBuilder 
{
	
	private static final boolean IGNORE_UNBOUND_UPDATED_VARS = true;
	
	public static GDFGraph constructGlobalDataFlowGraph( Program prog, Summary summary )
		throws DMLRuntimeException, HopsException
	{
		Timing time = new Timing(true);
		
		HashMap<String, GDFNode> roots = new HashMap<>();
		for( ProgramBlock pb : prog.getProgramBlocks() )
			constructGDFGraph( pb, roots );
		
		//create GDF graph root nodes 
		ArrayList<GDFNode> ret = new ArrayList<>();
		for( GDFNode root : roots.values() )
			if( !(root instanceof GDFCrossBlockNode) )
				ret.add(root);
		
		//create GDF graph
		GDFGraph graph = new GDFGraph(prog, ret);
		
		summary.setTimeGDFGraph(time.stop());
		return graph;
	}
	
	@SuppressWarnings("unchecked")
	private static void constructGDFGraph( ProgramBlock pb, HashMap<String, GDFNode> roots ) 
		throws DMLRuntimeException, HopsException
	{
		if (pb instanceof FunctionProgramBlock )
		{
			throw new DMLRuntimeException("FunctionProgramBlocks not implemented yet.");
		}
		else if (pb instanceof WhileProgramBlock)
		{
			WhileProgramBlock wpb = (WhileProgramBlock) pb;
			WhileStatementBlock wsb = (WhileStatementBlock) pb.getStatementBlock();		
			//construct predicate node (conceptually sequence of from/to/incr)
			GDFNode pred = constructGDFGraph(wsb.getPredicateHops(), wpb, new HashMap<Long, GDFNode>(), roots);
			HashMap<String,GDFNode> inputs = constructLoopInputNodes(wpb, wsb, roots);
			HashMap<String,GDFNode> lroots = (HashMap<String, GDFNode>) inputs.clone();
			//process childs blocks
			for( ProgramBlock pbc : wpb.getChildBlocks() )
				constructGDFGraph(pbc, lroots);
			HashMap<String,GDFNode> outputs = constructLoopOutputNodes(wsb, lroots);
			GDFLoopNode lnode = new GDFLoopNode(wpb, pred, inputs, outputs );
			//construct crossblock nodes
			constructLoopOutputCrossBlockNodes(wsb, lnode, outputs, roots, wpb);
		}	
		else if (pb instanceof IfProgramBlock)
		{
			IfProgramBlock ipb = (IfProgramBlock) pb;
			IfStatementBlock isb = (IfStatementBlock) pb.getStatementBlock();
			//construct predicate
			if( isb.getPredicateHops()!=null ) {
				Hop pred = isb.getPredicateHops();
				roots.put(pred.getName(), constructGDFGraph(pred, ipb, new HashMap<Long,GDFNode>(), roots));
			}
			//construct if and else branch separately
			HashMap<String,GDFNode> ifRoots = (HashMap<String, GDFNode>) roots.clone();
			HashMap<String,GDFNode> elseRoots = (HashMap<String, GDFNode>) roots.clone();
			for( ProgramBlock pbc : ipb.getChildBlocksIfBody() )
				constructGDFGraph(pbc, ifRoots);
			if( ipb.getChildBlocksElseBody()!=null )
				for( ProgramBlock pbc : ipb.getChildBlocksElseBody() )
					constructGDFGraph(pbc, elseRoots);
			//merge data flow roots (if no else, elseRoots refer to original roots)
			reconcileMergeIfProgramBlockOutputs(ifRoots, elseRoots, roots, ipb);
		}
		else if (pb instanceof ForProgramBlock) //incl parfor
		{
			ForProgramBlock fpb = (ForProgramBlock) pb;
			ForStatementBlock fsb = (ForStatementBlock)pb.getStatementBlock();
			//construct predicate node (conceptually sequence of from/to/incr)
			GDFNode pred = constructForPredicateNode(fpb, fsb, roots);
			HashMap<String,GDFNode> inputs = constructLoopInputNodes(fpb, fsb, roots);
			HashMap<String,GDFNode> lroots = (HashMap<String, GDFNode>) inputs.clone();
			//process childs blocks
			for( ProgramBlock pbc : fpb.getChildBlocks() )
				constructGDFGraph(pbc, lroots);
			HashMap<String,GDFNode> outputs = constructLoopOutputNodes(fsb, lroots);
			GDFLoopNode lnode = new GDFLoopNode(fpb, pred, inputs, outputs );
			//construct crossblock nodes
			constructLoopOutputCrossBlockNodes(fsb, lnode, outputs, roots, fpb);
		}
		else //last-level program block
		{
			StatementBlock sb = pb.getStatementBlock();
			ArrayList<Hop> hops = sb.getHops();
			if( hops != null )
			{
				//create new local memo structure for local dag
				HashMap<Long, GDFNode> lmemo = new HashMap<>();
				for( Hop hop : hops )
				{
					//recursively construct GDF graph for hop dag root
					GDFNode root = constructGDFGraph(hop, pb, lmemo, roots);
					if( root == null )
						throw new HopsException( "GDFGraphBuilder: failed to constuct dag root for: "+Explain.explain(hop) );
					
					//create cross block nodes for all transient writes
					if( hop instanceof DataOp && ((DataOp)hop).getDataOpType()==DataOpTypes.TRANSIENTWRITE )
						root = new GDFCrossBlockNode(hop, pb, root, hop.getName());
					
					//add GDF root node to global roots 
					roots.put(hop.getName(), root);
				}
			}
			
		}
	}
	
	private static GDFNode constructGDFGraph( Hop hop, ProgramBlock pb, HashMap<Long, GDFNode> lmemo, HashMap<String, GDFNode> roots )
	{
		if( lmemo.containsKey(hop.getHopID()) )
			return lmemo.get(hop.getHopID());
		
		//process childs recursively first
		ArrayList<GDFNode> inputs = new ArrayList<>();
		for( Hop c : hop.getInput() )
			inputs.add( constructGDFGraph(c, pb, lmemo, roots) );
		
		//connect transient reads to existing roots of data flow graph 
		if( hop instanceof DataOp && ((DataOp)hop).getDataOpType()==DataOpTypes.TRANSIENTREAD ){
			inputs.add(roots.get(hop.getName()));
		}
		
		//add current hop
		GDFNode gnode = new GDFNode(hop, pb, inputs);
				
		//add GDF node of updated variables to global roots (necessary for loops, where updated local
		//variables might never be bound to their logical variables names
		if( !IGNORE_UNBOUND_UPDATED_VARS ) {
			//NOTE: currently disabled because unnecessary, if no transientwrite by definition included in other transientwrite
			if( pb.getStatementBlock()!=null && pb.getStatementBlock().variablesUpdated().containsVariable(hop.getName()) ) {
				roots.put(hop.getName(), gnode);
			}
		}
		
		//memoize current node
		lmemo.put(hop.getHopID(), gnode);
		
		return gnode;
	}
	
	private static GDFNode constructForPredicateNode(ForProgramBlock fpb, ForStatementBlock fsb, HashMap<String, GDFNode> roots)
	{
		HashMap<Long, GDFNode> memo = new HashMap<>();
		GDFNode from = (fsb.getFromHops()!=null)? constructGDFGraph(fsb.getFromHops(), fpb, memo, roots) : null;
		GDFNode to = (fsb.getToHops()!=null)? constructGDFGraph(fsb.getToHops(), fpb, memo, roots) : null;
		GDFNode incr = (fsb.getIncrementHops()!=null)? constructGDFGraph(fsb.getIncrementHops(), fpb, memo, roots) : null;
		ArrayList<GDFNode> inputs = new ArrayList<>();
		inputs.add(from);
		inputs.add(to);
		inputs.add(incr);
		//TODO for predicates 
		GDFNode pred = new GDFNode(null, fpb, inputs );
		
		return pred;
	}
	
	private static HashMap<String, GDFNode> constructLoopInputNodes( ProgramBlock fpb, StatementBlock fsb, HashMap<String, GDFNode> roots ) 
		throws DMLRuntimeException
	{
		HashMap<String, GDFNode> ret = new HashMap<>();
		Set<String> invars = fsb.variablesRead().getVariableNames();
		for( String var : invars ) {
			if( fsb.liveIn().containsVariable(var) ) {
				GDFNode node = roots.get(var);
				if( node == null )
					throw new DMLRuntimeException("GDFGraphBuilder: Non-existing input node for variable: "+var);
				ret.put(var, node);
			}
		}
		
		return ret;
	}
	
	private static HashMap<String, GDFNode> constructLoopOutputNodes( StatementBlock fsb, HashMap<String, GDFNode> roots ) 
		throws HopsException
	{
		HashMap<String, GDFNode> ret = new HashMap<>();
		
		Set<String> outvars = fsb.variablesUpdated().getVariableNames();
		for( String var : outvars ) 
		{
			GDFNode node = roots.get(var);
			
			//handle non-existing nodes
			if( node == null ) {
				if( !IGNORE_UNBOUND_UPDATED_VARS )
					throw new HopsException( "GDFGraphBuilder: failed to constuct loop output for variable: "+var );	
				else
					continue; //skip unbound updated variables	
			}
			
			//add existing node to loop outputs 
			ret.put(var, node);
		}
		
		return ret;
	}
	
	private static void reconcileMergeIfProgramBlockOutputs( HashMap<String, GDFNode> ifRoots, HashMap<String, GDFNode> elseRoots, HashMap<String, GDFNode> roots, IfProgramBlock pb )
	{
		//merge same variable names, different data
		//( incl add new vars from if branch if node2==null)
		for( Entry<String, GDFNode> e : ifRoots.entrySet() ){
			GDFNode node1 = e.getValue();
			GDFNode node2 = elseRoots.get(e.getKey()); //original or new
			if( node1 != node2 )
				node1 = new GDFCrossBlockNode(null, pb, node1, node2, e.getKey() );
			roots.put(e.getKey(), node1);	
		}
		
		//add new vars from else branch 
		for( Entry<String, GDFNode> e : elseRoots.entrySet() ){
			if( !ifRoots.containsKey(e.getKey()) )
				roots.put(e.getKey(), e.getValue());	
		}
	}
	
	private static void constructLoopOutputCrossBlockNodes(StatementBlock sb, GDFLoopNode loop, HashMap<String, GDFNode> loutputs, HashMap<String, GDFNode> roots, ProgramBlock pb)
	{
		//iterate over all output (updated) variables
		for( Entry<String,GDFNode> e : loutputs.entrySet() ) 
		{
			//create crossblocknode, if updated variable is also in liveout
			if( sb.liveOut().containsVariable(e.getKey()) ) {
				GDFCrossBlockNode node = null;
				if( roots.containsKey(e.getKey()) )
					node = new GDFCrossBlockNode(null, pb, roots.get(e.getKey()), loop, e.getKey()); //MERGE
				else
					node = new GDFCrossBlockNode(null, pb, loop, e.getKey()); //PLAIN
				roots.put(e.getKey(), node);
			}
		}
	}
}

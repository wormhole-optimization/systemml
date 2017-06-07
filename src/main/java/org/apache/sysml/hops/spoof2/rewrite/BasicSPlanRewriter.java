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

package org.apache.sysml.hops.spoof2.rewrite;

import java.util.ArrayList;

import org.apache.sysml.hops.spoof2.plan.SNode;

/**
 * This program rewriter applies a variety of rule-based rewrites
 * on all hop dags of the given program in one pass over the entire
 * program. 
 * 
 */
public class BasicSPlanRewriter 
{
	private ArrayList<SPlanRewriteRule> _ruleSet = null;
	
	public BasicSPlanRewriter() {
		//initialize ruleSet (with fixed rewrite order)
		_ruleSet = new ArrayList<SPlanRewriteRule>();
		
		_ruleSet.add(new RewriteAggregateElimination());
		_ruleSet.add(new RewriteDistributiveSumProduct());
		_ruleSet.add(new RewriteTransposeElimination());
	}
	
	public ArrayList<SNode> rewriteSPlan(ArrayList<SNode> roots) {
		if( roots == null )
			return roots;

		//one pass rewrite-descend (rewrite created pattern)
		SNode.resetVisited(roots);
		for( SNode node : roots )
			rRewriteSPlan( node, false );

		//one pass descend-rewrite (for rollup) 
		SNode.resetVisited(roots);
		for( SNode node : roots )
			rRewriteSPlan( node, true );
		
		return roots;
	}

	private void rRewriteSPlan(SNode node, boolean descendFirst) {
		if( node.isVisited() )
			return;
		
		//recursively process children
		for( int i=0; i<node.getInput().size(); i++)
		{
			SNode ci = node.getInput().get(i);
			
			//process childs recursively first (to allow roll-up)
			if( descendFirst )
				rRewriteSPlan(ci, descendFirst); 
			
			//apply actual rewrite rules
			for( SPlanRewriteRule r : _ruleSet )
				ci = r.rewriteNode(node, ci, i);

			//process childs recursively after rewrites (to investigate pattern newly created by rewrites)
			if( !descendFirst )
				rRewriteSPlan(ci, descendFirst);
		}

		node.setVisited();
	}
}

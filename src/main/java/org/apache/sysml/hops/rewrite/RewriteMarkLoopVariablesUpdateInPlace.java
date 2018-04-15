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

package org.apache.sysml.hops.rewrite;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.apache.sysml.api.DMLScript;
import org.apache.sysml.api.DMLScript.RUNTIME_PLATFORM;
import org.apache.sysml.hops.DataOp;
import org.apache.sysml.hops.Hop;
import org.apache.sysml.hops.Hop.OpOp1;
import org.apache.sysml.hops.LeftIndexingOp;
import org.apache.sysml.hops.UnaryOp;
import org.apache.sysml.parser.ForStatement;
import org.apache.sysml.parser.ForStatementBlock;
import org.apache.sysml.parser.IfStatement;
import org.apache.sysml.parser.IfStatementBlock;
import org.apache.sysml.parser.StatementBlock;
import org.apache.sysml.parser.VariableSet;
import org.apache.sysml.parser.WhileStatement;
import org.apache.sysml.parser.WhileStatementBlock;
import org.apache.sysml.parser.Expression.DataType;

/**
 * Rule: Mark loop variables that are only read/updated through cp left indexing
 * for update in-place.
 * 
 */
public class RewriteMarkLoopVariablesUpdateInPlace extends StatementBlockRewriteRule
{
	@Override
	public boolean createsSplitDag() {
		return false;
	}
	
	@Override
	public List<StatementBlock> rewriteStatementBlock(StatementBlock sb, ProgramRewriteStatus status)
	{
		if( DMLScript.rtplatform == RUNTIME_PLATFORM.HADOOP
			|| DMLScript.rtplatform == RUNTIME_PLATFORM.SPARK )
		{
			// nothing to do here, return original statement block
			return Arrays.asList(sb);
		}
		
		if( sb instanceof WhileStatementBlock || sb instanceof ForStatementBlock ) //incl parfor 
		{
			ArrayList<String> candidates = new ArrayList<>();
			VariableSet updated = sb.variablesUpdated();
			VariableSet liveout = sb.liveOut();
			
			for( String varname : updated.getVariableNames() ) {
				if( updated.getVariable(varname).getDataType()==DataType.MATRIX
					&& liveout.containsVariable(varname) ) //exclude local vars 
				{
					if( sb instanceof WhileStatementBlock ) {
						WhileStatement wstmt = (WhileStatement) sb.getStatement(0);
						if( rIsApplicableForUpdateInPlace(wstmt.getBody(), varname) )
							candidates.add(varname);
					}
					else if( sb instanceof ForStatementBlock ) {
						ForStatement wstmt = (ForStatement) sb.getStatement(0);
						if( rIsApplicableForUpdateInPlace(wstmt.getBody(), varname) )
							candidates.add(varname);
					}
				}
			}	
			
			sb.setUpdateInPlaceVars(candidates);
		}
			
		//return modified statement block
		return Arrays.asList(sb);
	}
	
	private boolean rIsApplicableForUpdateInPlace( ArrayList<StatementBlock> sbs, String varname ) 
	{
		//NOTE: no function statement blocks / predicates considered because function call would 
		//render variable as not applicable and predicates don't allow assignments; further reuse 
		//of loop candidates as child blocks already processed
		
		//recursive invocation
		boolean ret = true;
		for( StatementBlock sb : sbs ) {
			if( !sb.variablesRead().containsVariable(varname)
				&& !sb.variablesUpdated().containsVariable(varname) )
				continue; //valid wrt update-in-place
			
			if( sb instanceof WhileStatementBlock || sb instanceof ForStatementBlock ) {
				ret &= sb.getUpdateInPlaceVars().contains(varname);
			}
			else if( sb instanceof IfStatementBlock ) {
				IfStatementBlock isb = (IfStatementBlock) sb;
				IfStatement istmt = (IfStatement)isb.getStatement(0);
				ret &= rIsApplicableForUpdateInPlace(istmt.getIfBody(), varname);
				if( ret && istmt.getElseBody() != null )
					ret &= rIsApplicableForUpdateInPlace(istmt.getElseBody(), varname);	
			}
			else {
				if( sb.getHops() != null )
					for( Hop hop : sb.getHops() ) 
						ret &= isApplicableForUpdateInPlace(hop, varname);
			}
			
			//early abort if not applicable
			if( !ret ) break;
		}
		
		return ret;
	}
	
	private static boolean isApplicableForUpdateInPlace( Hop hop, String varname )
	{
		if( !hop.getName().equals(varname) )
			return true;
	
		//valid if read/updated by leftindexing 
		//CP exec type not evaluated here as no lops generated yet 
		boolean validLix = hop instanceof DataOp 
			&& hop.isMatrix() && hop.getInput().get(0).isMatrix()
			&& hop.getInput().get(0) instanceof LeftIndexingOp
			&& hop.getInput().get(0).getInput().get(0) instanceof DataOp
			&& hop.getInput().get(0).getInput().get(0).getName().equals(varname);
		
		//valid if only safe consumers of left indexing input
		if( validLix ) {
			for( Hop p : hop.getInput().get(0).getInput().get(0).getParent() ) {
				validLix &= ( p == hop.getInput().get(0)  //lix
						|| (p instanceof UnaryOp && ((UnaryOp)p).getOp()==OpOp1.NROW)
						|| (p instanceof UnaryOp && ((UnaryOp)p).getOp()==OpOp1.NCOL));
			} 
		}
		
		return validLix;
	}
	
	@Override
	public List<StatementBlock> rewriteStatementBlocks(List<StatementBlock> sbs, ProgramRewriteStatus sate) {
		return sbs;
	}
}

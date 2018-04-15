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

package org.apache.sysml.hops.ipa;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;
import java.util.stream.Collectors;

import org.apache.sysml.hops.FunctionOp;
import org.apache.sysml.hops.Hop;
import org.apache.sysml.hops.HopsException;
import org.apache.sysml.hops.Hop.DataOpTypes;
import org.apache.sysml.hops.Hop.OpOpN;
import org.apache.sysml.hops.rewrite.HopRewriteUtils;
import org.apache.sysml.parser.DMLProgram;
import org.apache.sysml.parser.ExternalFunctionStatement;
import org.apache.sysml.parser.ForStatement;
import org.apache.sysml.parser.ForStatementBlock;
import org.apache.sysml.parser.FunctionStatement;
import org.apache.sysml.parser.FunctionStatementBlock;
import org.apache.sysml.parser.IfStatement;
import org.apache.sysml.parser.IfStatementBlock;
import org.apache.sysml.parser.StatementBlock;
import org.apache.sysml.parser.WhileStatement;
import org.apache.sysml.parser.WhileStatementBlock;

public class FunctionCallGraph 
{
	//internal function key for main program (underscore 
	//prevents any conflicts with user-defined functions)
	private static final String MAIN_FUNCTION_KEY = "_main"; 
	
	//unrolled function call graph, in call direction
	//(mapping from function keys to called function keys)
	private final HashMap<String, HashSet<String>> _fGraph;
	
	//program-wide function call operators per target function
	//(mapping from function keys to set of its function calls)
	private final HashMap<String, ArrayList<FunctionOp>> _fCalls;
	private final HashMap<String, ArrayList<StatementBlock>> _fCallsSB;
	
	//subset of direct or indirect recursive functions
	private final HashSet<String> _fRecursive;
	
	private final boolean _containsEval;
	
	/**
	 * Constructs the function call graph for all functions
	 * reachable from the main program. 
	 * 
	 * @param prog dml program of given script
	 */
	public FunctionCallGraph(DMLProgram prog) {
		_fGraph = new HashMap<>();
		_fCalls = new HashMap<>();
		_fCallsSB = new HashMap<>();
		_fRecursive = new HashSet<>();
		_containsEval = constructFunctionCallGraph(prog);
	}
	
	/**
	 * Constructs the function call graph for all functions
	 * reachable from the given statement block. 
	 * 
	 * @param sb statement block (potentially hierarchical)
	 */
	public FunctionCallGraph(StatementBlock sb) {
		_fGraph = new HashMap<>();
		_fCalls = new HashMap<>();
		_fCallsSB = new HashMap<>();
		_fRecursive = new HashSet<>();
		_containsEval = constructFunctionCallGraph(sb);
	}

	/**
	 * Returns all functions called from the given function. 
	 * 
	 * @param fnamespace function namespace
	 * @param fname function name
	 * @return set of function keys (namespace and name)
	 */
	public Set<String> getCalledFunctions(String fnamespace, String fname) {
		return getCalledFunctions(
			DMLProgram.constructFunctionKey(fnamespace, fname));
	}
	
	/**
	 * Returns all functions called from the given function. 
	 * 
	 * @param fkey function key of calling function, null indicates the main program
	 * @return set of function keys (namespace and name)
	 */
	public Set<String> getCalledFunctions(String fkey) {
		String lfkey = (fkey == null) ? MAIN_FUNCTION_KEY : fkey;
		return _fGraph.get(lfkey);
	}
	
	/**
	 * Returns all function operators calling the given function.
	 * 
	 * @param fkey function key of called function,
	 *      null indicates the main program and returns an empty list
	 * @return list of function call hops 
	 */
	public List<FunctionOp> getFunctionCalls(String fkey) {
		//main program cannot have function calls
		if( fkey == null )
			return Collections.emptyList();
		return _fCalls.get(fkey);
	}
	
	/**
	 * Returns all statement blocks that contain a function operator
	 * calling the given function.
	 * 
	 * @param fkey function key of called function,
	 *      null indicates the main program and returns an empty list
	 * @return list of statement blocks
	 */
	public List<StatementBlock> getFunctionCallsSB(String fkey) {
		//main program cannot have function calls
		if( fkey == null )
			return Collections.emptyList();
		return _fCallsSB.get(fkey);
	}
	
	/**
	 * Removes all calls of the given function.
	 * 
	 * @param fkey function key of called function,
	 *      null indicates the main program, which has no affect
	 */
	public void removeFunctionCalls(String fkey) {
		_fCalls.remove(fkey);
		_fCallsSB.remove(fkey);
		_fRecursive.remove(fkey);
		_fGraph.remove(fkey);
		for( Entry<String, HashSet<String>> e : _fGraph.entrySet() )
			e.getValue().removeIf(s -> s.equals(fkey));
	}
	
	/**
	 * Indicates if the given function is either directly or indirectly recursive.
	 * An example of an indirect recursive function is foo2 in the following call
	 * chain: foo1 -&gt; foo2 -&gt; foo1.
	 * 
	 * @param fnamespace function namespace
	 * @param fname function name
	 * @return true if the given function is recursive, false otherwise
	 */
	public boolean isRecursiveFunction(String fnamespace, String fname) {
		return isRecursiveFunction(
			DMLProgram.constructFunctionKey(fnamespace, fname));
	}
	
	/**
	 * Indicates if the given function is either directly or indirectly recursive.
	 * An example of an indirect recursive function is foo2 in the following call
	 * chain: foo1 -&gt; foo2 -&gt; foo1.
	 * 
	 * @param fkey function key of calling function, null indicates the main program
	 * @return true if the given function is recursive, false otherwise
	 */
	public boolean isRecursiveFunction(String fkey) {
		String lfkey = (fkey == null) ? MAIN_FUNCTION_KEY : fkey;
		return _fRecursive.contains(lfkey);
	}
	
	/**
	 * Returns all functions that are reachable either directly or indirectly
	 * form the main program, except the main program itself.
	 * 
	 * @return set of function keys (namespace and name)
	 */
	public Set<String> getReachableFunctions() {
		return getReachableFunctions(Collections.emptySet());
	}
	
	/**
	 * Returns all functions that are reachable either directly or indirectly
	 * form the main program, except the main program itself and the given 
	 * blacklist of function names.
	 * 
	 * @param blacklist list of function keys to exclude
	 * @return set of function keys (namespace and name)
	 */
	public Set<String> getReachableFunctions(Set<String> blacklist) {
		return _fGraph.keySet().stream()
			.filter(p -> !blacklist.contains(p) && !MAIN_FUNCTION_KEY.equals(p))
			.collect(Collectors.toSet());
	}
	
	/**
	 * Indicates if the given function is reachable either directly or indirectly
	 * from the main program.
	 * 
	 * @param fnamespace function namespace
	 * @param fname function name
	 * @return true if the given function is reachable, false otherwise
	 */
	public boolean isReachableFunction(String fnamespace, String fname) {
		return isReachableFunction(
			DMLProgram.constructFunctionKey(fnamespace, fname));
	}
	
	/**
	 * Indicates if the given function is reachable either directly or indirectly
	 * from the main program.
	 * 
	 * @param fkey function key of calling function, null indicates the main program
	 * @return true if the given function is reachable, false otherwise
	 */
	public boolean isReachableFunction(String fkey) {
		String lfkey = (fkey == null) ? MAIN_FUNCTION_KEY : fkey;
		return _fGraph.containsKey(lfkey);
	}
	
	/**
	 * Indicates if the function call graph, i.e., functions that are transitively
	 * reachable from the main program, contains a second-order eval call, which
	 * prohibits the removal of unused functions.
	 * 
	 * @return true if the function call graph contains an eval call.
	 */
	public boolean containsEvalCall() {
		return _containsEval;
	}
	
	private boolean constructFunctionCallGraph(DMLProgram prog) {
		if( !prog.hasFunctionStatementBlocks() )
			return false; //early abort if prog without functions
		
		boolean ret = false;
		try {
			Stack<String> fstack = new Stack<>();
			HashSet<String> lfset = new HashSet<>();
			_fGraph.put(MAIN_FUNCTION_KEY, new HashSet<String>());
			for( StatementBlock sblk : prog.getStatementBlocks() )
				ret |= rConstructFunctionCallGraph(MAIN_FUNCTION_KEY, sblk, fstack, lfset);
		}
		catch(HopsException ex) {
			throw new RuntimeException(ex);
		}
		return ret;
	}
	
	private boolean constructFunctionCallGraph(StatementBlock sb) {
		if( !sb.getDMLProg().hasFunctionStatementBlocks() )
			return false; //early abort if prog without functions
		
		try {
			Stack<String> fstack = new Stack<>();
			HashSet<String> lfset = new HashSet<>();
			_fGraph.put(MAIN_FUNCTION_KEY, new HashSet<String>());
			return rConstructFunctionCallGraph(MAIN_FUNCTION_KEY, sb, fstack, lfset);
		}
		catch(HopsException ex) {
			throw new RuntimeException(ex);
		}
	}
	
	private boolean rConstructFunctionCallGraph(String fkey, StatementBlock sb, Stack<String> fstack, HashSet<String> lfset) {
		boolean ret = false;
		if (sb instanceof WhileStatementBlock) {
			WhileStatement ws = (WhileStatement)sb.getStatement(0);
			for (StatementBlock current : ws.getBody())
				ret |= rConstructFunctionCallGraph(fkey, current, fstack, lfset);
		} 
		else if (sb instanceof IfStatementBlock) {
			IfStatement ifs = (IfStatement) sb.getStatement(0);
			for (StatementBlock current : ifs.getIfBody())
				ret |= rConstructFunctionCallGraph(fkey, current, fstack, lfset);
			for (StatementBlock current : ifs.getElseBody())
				ret |= rConstructFunctionCallGraph(fkey, current, fstack, lfset);
		} 
		else if (sb instanceof ForStatementBlock) {
			ForStatement fs = (ForStatement)sb.getStatement(0);
			for (StatementBlock current : fs.getBody())
				ret |= rConstructFunctionCallGraph(fkey, current, fstack, lfset);
		} 
		else if (sb instanceof FunctionStatementBlock) {
			FunctionStatement fsb = (FunctionStatement) sb.getStatement(0);
			for (StatementBlock current : fsb.getBody())
				ret |= rConstructFunctionCallGraph(fkey, current, fstack, lfset);
		} 
		else {
			// For generic StatementBlock
			ArrayList<Hop> hopsDAG = sb.getHops();
			if( hopsDAG == null || hopsDAG.isEmpty() ) 
				return false; //nothing to do
			
			//function ops can only occur as root nodes of the dag
			for( Hop h : hopsDAG ) {
				if( h instanceof FunctionOp ) {
					FunctionOp fop = (FunctionOp) h;
					String lfkey = fop.getFunctionKey();
					//keep all function operators
					if( !_fCalls.containsKey(lfkey) ) {
						_fCalls.put(lfkey, new ArrayList<>());
						_fCallsSB.put(lfkey, new ArrayList<>());
					}
					_fCalls.get(lfkey).add(fop);
					_fCallsSB.get(lfkey).add(sb);
					
					//prevent redundant call edges
					if( lfset.contains(lfkey) || fop.getFunctionNamespace().equals(DMLProgram.INTERNAL_NAMESPACE) )
						continue;
					
					if( !_fGraph.containsKey(lfkey) )
						_fGraph.put(lfkey, new HashSet<String>());
					
					//recursively construct function call dag
					if( !fstack.contains(lfkey) ) {
						fstack.push(lfkey);
						_fGraph.get(fkey).add(lfkey);
						
						FunctionStatementBlock fsb = sb.getDMLProg()
							.getFunctionStatementBlock(fop.getFunctionNamespace(), fop.getFunctionName());
						FunctionStatement fs = (FunctionStatement) fsb.getStatement(0);
						for( StatementBlock csb : fs.getBody() )
							ret |= rConstructFunctionCallGraph(lfkey, csb, fstack, new HashSet<String>());
						fstack.pop();
					}
					//recursive function call
					else {
						_fGraph.get(fkey).add(lfkey);
						_fRecursive.add(lfkey);
					
						//mark indirectly recursive functions as recursive
						int ix = fstack.indexOf(lfkey);
						for( int i=ix+1; i<fstack.size(); i++ )
							_fRecursive.add(fstack.get(i));
					}
					
					//mark as visited for current function call context
					lfset.add( lfkey );
					
					//handle second order external functions
					FunctionStatementBlock fsb = sb.getDMLProg().getFunctionStatementBlock(lfkey);
					if( fsb != null && fsb.getStatement(0) instanceof ExternalFunctionStatement
						&& ((ExternalFunctionStatement)fsb.getStatement(0)).isSecondOrder() ) {
						ret = true;
					}
				}
				else if( HopRewriteUtils.isData(h, DataOpTypes.TRANSIENTWRITE)
					&& HopRewriteUtils.isNary(h.getInput().get(0), OpOpN.EVAL) ) {
					//NOTE: after RewriteSplitDagDataDependentOperators, eval operators
					//will always appear as childs to root nodes which allows for an
					//efficient existence check without DAG traversal.
					ret = true;
				}
			}
		}
		
		return ret;
	}
}

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

import org.apache.sysml.runtime.controlprogram.ProgramBlock;

public class GDFLoopNode extends GDFNode
{
	
	private GDFNode _predicate = null; 
	private HashMap<String,GDFNode> _linputs = null; //all read variables
	private HashMap<String,GDFNode> _loutputs = null; //all updated variables, not necessarily liveout
	
	public GDFLoopNode( ProgramBlock pb, GDFNode predicate, HashMap<String, GDFNode> inputs, HashMap<String,GDFNode> outputs )
	{
		super(null, pb, new ArrayList<>(inputs.values()));
		_type = NodeType.LOOP_NODE;
		_predicate = predicate;
		_linputs = inputs;
		_loutputs = outputs;
	}
	
	public HashMap<String, GDFNode> getLoopInputs()
	{
		return _linputs;
	}
	
	public HashMap<String, GDFNode> getLoopOutputs()
	{
		return _loutputs;
	}
	
	public GDFNode getLoopPredicate()
	{
		return _predicate;
	}
	
	@Override
	public String explain(String deps) 
	{
		String ldeps = (deps!=null) ? deps : "";
	
		//current node details
		return "LoopNode "+ldeps+" ["+_linputs.keySet().toString()+","+_loutputs.keySet().toString()+"]";
	}
}

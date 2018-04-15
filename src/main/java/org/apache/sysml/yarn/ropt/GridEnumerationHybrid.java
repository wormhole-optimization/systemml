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

package org.apache.sysml.yarn.ropt;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;

import org.apache.sysml.runtime.controlprogram.ProgramBlock;

/**
 * Composite overlay of hybrid and exp grid.
 * 
 */
public class GridEnumerationHybrid extends GridEnumeration
{
	public GridEnumerationHybrid( ArrayList<ProgramBlock> prog, long min, long max ) {
		super(prog, min, max);
	}
	
	@Override
	public ArrayList<Long> enumerateGridPoints() {
		GridEnumeration ge1 = new GridEnumerationMemory(_prog, _min, _max);
		GridEnumeration ge2 = new GridEnumerationExp(_prog, _min, _max);
		
		//ensure distinct points
		HashSet<Long> hs = new HashSet<>();
		hs.addAll( ge1.enumerateGridPoints() );
		hs.addAll( ge2.enumerateGridPoints() );
		
		//create sorted output list
		ArrayList<Long> ret = new ArrayList<>();
		for( Long val : hs )
			ret.add(val);
		Collections.sort(ret); //asc
		
		return ret;
	}
}

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

import org.apache.sysml.runtime.controlprogram.ProgramBlock;

public class GridEnumerationExp extends GridEnumeration
{
	
	public static final double DEFAULT_FACTOR = 2;

	private double _factor = -1;
	
	public GridEnumerationExp( ArrayList<ProgramBlock> prog, long min, long max ) {
		super(prog, min, max);
		_factor = DEFAULT_FACTOR;
	}
	
	public void setFactor( double factor ) {
		_factor = factor;
	}
	
	@Override
	public ArrayList<Long> enumerateGridPoints() 
	{
		ArrayList<Long> ret = new ArrayList<>();
		long v = _min;
		while( v < _max ) {
			ret.add( v );
			v *= _factor;
		}
		ret.add(_max);
		
		return ret;
	}
}

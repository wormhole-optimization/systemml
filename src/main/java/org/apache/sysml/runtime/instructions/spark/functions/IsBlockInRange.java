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

package org.apache.sysml.runtime.instructions.spark.functions;

import org.apache.spark.api.java.function.Function;

import scala.Tuple2;

import org.apache.sysml.runtime.matrix.MatrixCharacteristics;
import org.apache.sysml.runtime.matrix.data.MatrixBlock;
import org.apache.sysml.runtime.matrix.data.MatrixIndexes;
import org.apache.sysml.runtime.util.UtilFunctions;

public class IsBlockInRange implements Function<Tuple2<MatrixIndexes,MatrixBlock>, Boolean> 
{
	private static final long serialVersionUID = 5849687296021280540L;
	
	private long _rl; long _ru; long _cl; long _cu;
	private int _brlen; int _bclen;
	
	public IsBlockInRange(long rl, long ru, long cl, long cu, MatrixCharacteristics mc) {
		_rl = rl;
		_ru = ru;
		_cl = cl;
		_cu = cu;
		_brlen = mc.getRowsPerBlock();
		_bclen = mc.getColsPerBlock();
	}

	@Override
	public Boolean call(Tuple2<MatrixIndexes, MatrixBlock> kv) 
		throws Exception 
	{
		return UtilFunctions.isInBlockRange(kv._1(), _brlen, _bclen, _rl, _ru, _cl, _cu);
	}
}

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


package org.apache.sysml.runtime.matrix.data;

import java.io.DataInput;
import java.io.DataOutput;
import java.io.IOException;

public class TaggedMatrixIndexes extends Tagged<MatrixIndexes>
{	
	public TaggedMatrixIndexes(){}
	
	public TaggedMatrixIndexes(MatrixIndexes ix, byte t) {
		super(ix, t);
	}
	
	public TaggedMatrixIndexes(TaggedMatrixIndexes that) {
		tag = that.tag;
		base = that.base;
	}
	
	@Override
	public String toString() {
		return "k: "+base+", tag: "+tag;
	}
	
	@Override
	public void readFields(DataInput in) throws IOException {
		if( base == null ){
			base = new MatrixIndexes();
		}
		base.readFields(in);
		tag=in.readByte();
	}
	
	@Override
	public void write(DataOutput out) throws IOException {
		base.write(out);
		out.writeByte(tag);
	}
	
	public int compareTo(TaggedMatrixIndexes other) {
		int tmp = base.compareTo(other.base);
		if( tmp != 0 )
			return tmp;
		else if( tag!=other.tag )
			return tag-other.tag;
		return 0;
	}

	@Override
	public boolean equals(Object other)
	{
		if( !(other instanceof TaggedMatrixIndexes))
			return false;
		
		TaggedMatrixIndexes tother = (TaggedMatrixIndexes)other;
		return (base.equals(tother.base) && tag==tother.tag);
	}
	
	@Override
	public int hashCode() {
		 return base.hashCode() + tag;
	}

}

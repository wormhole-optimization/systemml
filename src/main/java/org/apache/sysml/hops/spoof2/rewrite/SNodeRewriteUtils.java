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

public class SNodeRewriteUtils 
{
	public static int getChildReferencePos( SNode parent, SNode child ) {
		return parent.getInput().indexOf(child);
	}
	
	public static void removeChildReference( SNode parent, SNode child ) {
		parent.getInput().remove( child );
		child.getParent().remove( parent );
	}
	
	public static void removeChildReferenceByPos( SNode parent, SNode child, int posChild ) {
		parent.getInput().remove( posChild );
		child.getParent().remove( parent );
	}

	public static void removeAllChildReferences( SNode parent )
	{
		//remove parent reference from all childs
		for( SNode child : parent.getInput() )
			child.getParent().remove(parent);
		
		//remove all child references
		parent.getInput().clear();
	}
	
	public static void addChildReference( SNode parent, SNode child ) {
		parent.getInput().add( child );
		child.getParent().add( parent );
	}
	
	public static void addChildReference( SNode parent, SNode child, int pos ){
		parent.getInput().add( pos, child );
		child.getParent().add( parent );
	}
	
	public static void rewireAllParentChildReferences( SNode hold, SNode hnew ) {
		ArrayList<SNode> parents = new ArrayList<SNode>(hold.getParent());
		for( SNode lparent : parents )
			SNodeRewriteUtils.replaceChildReference(lparent, hold, hnew);
	}
	
	public static void replaceChildReference( SNode parent, SNode inOld, SNode inNew ) {
		int pos = getChildReferencePos(parent, inOld);
		removeChildReferenceByPos(parent, inOld, pos);
		addChildReference(parent, inNew, pos);
	}
	
	public static void replaceChildReference( SNode parent, SNode inOld, SNode inNew, int pos ) {
		replaceChildReference(parent, inOld, inNew, pos, true);
	}
	
	public static void replaceChildReference( SNode parent, SNode inOld, SNode inNew, int pos, boolean refresh ) {
		removeChildReferenceByPos(parent, inOld, pos);
		addChildReference(parent, inNew, pos);
	}
	
	public static void cleanupUnreferenced( SNode... inputs ) {
		for( SNode input : inputs )
			if( input.getParent().isEmpty() )
				removeAllChildReferences(input);
	}
}

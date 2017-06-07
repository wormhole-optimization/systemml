package org.apache.sysml.hops.spoof2.rewrite;

import org.apache.sysml.hops.spoof2.plan.SNode;
import org.apache.sysml.hops.spoof2.plan.SNodeAggregate;
import org.apache.sysml.hops.spoof2.plan.SNodeNary;
import org.apache.sysml.hops.spoof2.plan.SNodeNary.NaryOp;

public class RewriteTransposeElimination extends SPlanRewriteRule
{
	@Override
	public SNode rewriteNode(SNode parent, SNode node, int pos) 
	{
		if( node instanceof SNodeAggregate && node.getInput().get(0) instanceof SNodeNary
			&& ((SNodeNary)node.getInput().get(0)).getOp()==NaryOp.TRANSPOSE ) {
			SNode input = node.getInput().get(0);
			SNodeRewriteUtils.replaceChildReference(node, input, 
				input.getInput().get(0));
			
			LOG.debug("Applied RewriteTransposeElimination.");
		}
		
		return node;
	}

}

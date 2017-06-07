package org.apache.sysml.hops.spoof2.rewrite;

import org.apache.sysml.hops.Hop.AggOp;
import org.apache.sysml.hops.spoof2.plan.SNode;
import org.apache.sysml.hops.spoof2.plan.SNodeAggregate;

public class RewriteAggregateElimination extends SPlanRewriteRule
{

	@Override
	public SNode rewriteNode(SNode parent, SNode node, int pos) {
		
		if( node instanceof SNodeAggregate 
			&& node.getInput().get(0) instanceof SNodeAggregate )
		{
			SNodeAggregate agg1 = (SNodeAggregate) node;
			SNodeAggregate agg2 = (SNodeAggregate) node.getInput().get(0);
			if( (agg1.getOp()==AggOp.SUM && agg2.getOp()==AggOp.SUM)
				||(agg1.getOp()==AggOp.MIN && agg2.getOp()==AggOp.MIN)
				||(agg1.getOp()==AggOp.MAX && agg2.getOp()==AggOp.MAX) )
			{
				SNodeRewriteUtils.replaceChildReference(
					agg1, agg2, agg2.getInput().get(0));
				LOG.debug("Applied RewriteAggregateElimination.");
			}
		}
		
		return node;
	}

}

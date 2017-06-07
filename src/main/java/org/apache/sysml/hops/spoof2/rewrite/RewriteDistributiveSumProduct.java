package org.apache.sysml.hops.spoof2.rewrite;

import java.util.ArrayList;
import java.util.List;

import org.apache.sysml.hops.Hop.AggOp;
import org.apache.sysml.hops.spoof2.plan.SNode;
import org.apache.sysml.hops.spoof2.plan.SNodeAggregate;
import org.apache.sysml.hops.spoof2.plan.SNodeNary;
import org.apache.sysml.hops.spoof2.plan.SNodeNary.NaryOp;

public class RewriteDistributiveSumProduct extends SPlanRewriteRule
{
	@Override
	public SNode rewriteNode(SNode parent, SNode node, int pos) {
		
		//pattern: agg(sum)-b(*)
		if( node instanceof SNodeAggregate && ((SNodeAggregate)node).getOp()==AggOp.SUM 
			&& node.getInput().get(0) instanceof SNodeNary 
			&& ((SNodeNary)node.getInput().get(0)).getOp()==NaryOp.MULT )
		{
			SNodeAggregate sum = (SNodeAggregate) node;
			SNodeNary mult = (SNodeNary) node.getInput().get(0);
			
			//check left/right aggregation pushdown
			int numApplied = 0;
			for( int i=0; i<2; i++ ) {
				SNode input = mult.getInput().get(i);
				if( !input.isScalar() ) {
					List<String> tgtSchema = new ArrayList<String>();
					List<Long> tgtDims = new ArrayList<Long>();
					//construct minimal target scheme for binary input
					for( String attr : input.getSchema() )
						if( sum.getSchema().contains(attr)
							|| mult.containsJoinCondition(attr) ) {
							tgtSchema.add(attr);
							tgtDims.add(input.getDim(attr));
						}
					//create new aggregate if potential for pre-agg
					if( input.getSchema().size() > tgtSchema.size() ) {
						SNodeAggregate sum2 = new SNodeAggregate(input, AggOp.SUM, tgtSchema);
						sum2.setDims(tgtDims.toArray(new Long[0]));
						SNodeRewriteUtils.replaceChildReference(mult, input, sum2);
						//update multiply dimensions and schema
						//TODO extend for row/column sums
						if( tgtSchema.isEmpty() ) { 
							mult.setDims(0L, 0L);
							mult.setSchema(mult.getInput().get(i).getSchema());
						}
						numApplied ++;
					}
				}
			}
			
			if( numApplied > 0 )
				LOG.debug("Applied RewriteDistributiveSumProduct (num="+numApplied+").");
		}
		
		return node;
	}

}

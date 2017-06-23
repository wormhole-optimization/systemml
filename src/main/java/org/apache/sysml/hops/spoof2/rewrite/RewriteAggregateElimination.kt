package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.Hop.AggOp
import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.SNodeAggregate

class RewriteAggregateElimination : SPlanRewriteRule() {

    override fun rewriteNode(parent: SNode, node: SNode, pos: Int): SNode {

        if (node is SNodeAggregate && node.inputs[0] is SNodeAggregate) {
            val agg1 = node
            val agg2 = node.inputs[0] as SNodeAggregate
            if (agg1.op == AggOp.SUM && agg2.op == AggOp.SUM
                    || agg1.op == AggOp.MIN && agg2.op == AggOp.MIN // shouldn't we do this for any identical aggregation ops?
                    || agg1.op == AggOp.MAX && agg2.op == AggOp.MAX) {
                SNodeRewriteUtils.replaceChildReference(agg1, agg2, agg2.inputs[0])
                if( SPlanRewriteRule.LOG.isDebugEnabled )
                    SPlanRewriteRule.LOG.debug("Applied RewriteAggregateElimination (agg(${agg1.id})-agg(${agg2.id})).")
            }
        } else if (node is SNodeAggregate && node.schema == node.inputs[0].schema) {
            // this rule looks dubious
            SNodeRewriteUtils.replaceChildReference(
                    parent, node, node.inputs[0])
            SPlanRewriteRule.LOG.debug("Applied RewriteAggregateElimination (equi schema) on agg(${node.id}).")
        }

        return node
    }

}

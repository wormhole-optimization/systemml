package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.SNodeAggregate

/**
 * 1. Combine two consecutive aggregates into one.
 * 2. Eliminate empty aggregates.
 */
class RewriteAggregateElim : SPlanRewriteRule() {

    companion object {
//        val allowedAggOps = setOf(AggOp.SUM, AggOp.MIN, AggOp.MAX, AggOp.)
    }

    override fun rewriteNode(parent: SNode, node: SNode, pos: Int): RewriteResult {
        return rRewriteNode(parent, node, false)
    }
    private tailrec fun rRewriteNode(parent: SNode, node: SNode, changed: Boolean): RewriteResult {
        if( node is SNodeAggregate ) {
            val agg1 = node
            val agg2 = node.input
            if( agg2 is SNodeAggregate && agg2.parents.size == 1 ) { // RewriteSplitCSE handles the foreign parent case
                if (agg1.op == agg2.op) {
                    // consecutive aggregates; let agg1 do all the aggregating
                    // eliminate agg2; connect agg1 to child of agg2
                    agg1.aggs += agg2.aggs
                    val agg2child = agg2.input
                    agg2child.parents -= agg2
                    agg1.input = agg2child
                    agg2child.parents += agg1
                    agg1.refreshSchema()
                    if (SPlanRewriteRule.LOG.isDebugEnabled)
                        SPlanRewriteRule.LOG.debug("RewriteAggregateElim on consecutive aggs ${agg1.id}-${agg2.id} to form $agg1.")
                    return rRewriteNode(parent, agg1, true)
                }
            }
            if( node.aggs.isEmpty() ) {
                // agg is empty; connect child to parent
                // handle multiple parents
                val child = node.inputs[0]
                SNodeRewriteUtils.removeAllChildReferences(node)
                SNodeRewriteUtils.replaceChildReference(parent, node, child)
                if (SPlanRewriteRule.LOG.isDebugEnabled)
                    SPlanRewriteRule.LOG.debug("RewriteAggregateElim on empty agg ${node.id} $node).")
                return rRewriteNode(parent, child, true)
            }
        }
        return if (changed) RewriteResult.NewNode(node) else RewriteResult.NoChange
    }

}

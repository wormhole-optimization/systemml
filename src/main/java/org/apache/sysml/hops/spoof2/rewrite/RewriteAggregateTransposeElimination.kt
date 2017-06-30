package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.spoof2.plan.SNode

/**
 * Eliminate transpose before aggregation if the transposed elements will be aggregated anyway.
 */
class RewriteAggregateTransposeElimination : SPlanRewriteRule() {
    override fun rewriteNode(parent: SNode, node: SNode, pos: Int): SNode {
//        if (node is SNodeAggregate && node.inputs[0] is SNodePermute) {
//            val perm = node.inputs[0] as SNodePermute
//            if( (perm.getSwitchedAttributes().toSet() - node.aggreateNames).isEmpty() ) {
//                SNodeRewriteUtils.replaceChildReference(node, perm, perm.inputs[0])
//                SPlanRewriteRule.LOG.debug("Applied RewriteAggregateTransposeElimination.")
//            }
//        }

        return node
    }

}

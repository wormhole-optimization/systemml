package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.Hop.AggOp
import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.SNodeAggregate
import org.apache.sysml.hops.spoof2.plan.SNodeNary
import org.apache.sysml.hops.spoof2.plan.SNodeNary.NaryOp

class RewritePushAggIntoMult : SPlanRewriteRule() {
    override fun rewriteNode(parent: SNode, node: SNode, pos: Int): SNode {

        //pattern: agg(sum)-b(*)
        if (node is SNodeAggregate && node.op == AggOp.SUM
                && node.inputs[0] is SNodeNary
                && (node.inputs[0] as SNodeNary).op == NaryOp.MULT) { // todo generalize to other multiply functions that are semiring to +
            val agg = node
            val mult = node.inputs[0] as SNodeNary
            // the attributes that occur in more than one input
            val joinAttrs = mult.getJoinLabelCounts().entrySet().filter { it.count > 1 }.map { it.element!! }

            //check left/right aggregation pushdown
            var numApplied = 0
            for (i in mult.inputs.indices) {
                val input = mult.inputs[i]
                // find indices that are neither in the output nor in the join condition
                val preAggAttrs = input.schema.names.filter { it !in agg.schema && it !in joinAttrs }
                if (preAggAttrs.isNotEmpty()) {
                    // pre-aggregate these indices!
                    val preAgg = SNodeAggregate(AggOp.SUM, input, preAggAttrs)
                    SNodeRewriteUtils.replaceChildReference(mult, input, preAgg)
                    mult.refreshSchema()
                    numApplied++
                }
            }

            if (numApplied > 0) {
                // check if the agg no longer needs some attributes
                val fullyPushed = agg.aggreateNames.filter { it !in mult.schema }
                agg.aggreateNames -= fullyPushed
                if( agg.aggreateNames.isEmpty() ) { // eliminate agg
                    SNodeRewriteUtils.removeAllChildReferences(agg) // clear node.inputs, child.parents
                    SNodeRewriteUtils.rewireAllParentChildReferences(agg, mult) // for each parent of node, change its input from node to child and add the parent to child
                }
                if( SPlanRewriteRule.LOG.isDebugEnabled )
                    SPlanRewriteRule.LOG.debug("Applied RewritePushAggIntoMult, num=$numApplied. Fully pushed: $fullyPushed."+(if(agg.aggreateNames.isEmpty())" Eliminate agg." else ""))
            }
        }

        return node
    }

}

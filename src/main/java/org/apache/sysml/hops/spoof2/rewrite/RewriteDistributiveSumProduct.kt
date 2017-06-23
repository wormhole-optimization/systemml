package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.Hop.AggOp
import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.SNodeAggregate
import org.apache.sysml.hops.spoof2.plan.SNodeNary
import org.apache.sysml.hops.spoof2.plan.SNodeNary.NaryOp

class RewriteDistributiveSumProduct : SPlanRewriteRule() {
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
                val preAggAttrs = input.schema.labels.filter { it !in agg.schema && it !in joinAttrs }
                if (preAggAttrs.isNotEmpty()) {
                    // pre-aggregate these indices!
                    val preAgg = SNodeAggregate(AggOp.SUM, input, preAggAttrs.toHashSet())
                    preAgg.updateSchema() // todo - automate this?
                    SNodeRewriteUtils.replaceChildReference(mult, input, preAgg)
                    mult.updateSchema()

                    numApplied++
                }
            }

            if (numApplied > 0)
                SPlanRewriteRule.LOG.debug("Applied RewriteDistributiveSumProduct (num=$numApplied).")
        }

        return node
    }

}

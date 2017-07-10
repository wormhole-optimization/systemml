package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.Hop.AggOp
import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.SNodeAggregate
import org.apache.sysml.hops.spoof2.plan.SNodeNary
import org.apache.sysml.hops.spoof2.plan.SNodeNary.NaryOp

/**
 * Pattern:
 * <pre>
 *      \ /    ->    \ /
 *       *     ->     +
 *     / | \   ->     |
 *    +  .. .. ->     *
 * \ /         -> \ / | \
 *  C          ->  C  .. ..
 * </pre>
 * and no foreign parents on +.
 */
class RewritePullAggAboveMult : SPlanRewriteRule() {
    override fun rewriteNode(parent: SNode, node: SNode, pos: Int): RewriteResult {
        if( node !is SNodeNary || node.op != NaryOp.MULT ) // todo generalize to other * functions that are semiring to +
            return RewriteResult.NoChange
        val mult = node
        var top = mult
        var numApplied = 0

        for (iMultToAgg in mult.inputs.indices) { // index of agg in mult
            val agg = mult.inputs[iMultToAgg]
            if( agg is SNodeAggregate
                    && agg.parents.size == 1
                    && agg.op == AggOp.SUM ) {
                val aggChild = agg.inputs[0]
                val iAggChildToAgg = aggChild.parents.indexOf(agg)
                aggChild.parents[iAggChildToAgg] = mult
                agg.inputs[0] = mult
                agg.parents.clear()
                agg.parents.addAll(mult.parents)
                // set mult.parents to agg
                mult.parents.forEach { multParent ->
                    for (iMultParentToMult in multParent.inputs.indices) {
                        if( multParent.inputs[iMultParentToMult] === mult )
                            multParent.inputs[iMultParentToMult] = agg
                    }
                }
                mult.inputs[iMultToAgg] = aggChild
                mult.parents.clear()
                mult.parents.add(agg)
                //
                mult.refreshSchema()
                agg.refreshSchema()
                if( top === node ) // original parents connect to the first pulled aggregate
                    top = agg      // a later rewrite rule will combine consecutive aggregates
                numApplied++
            }
        }
        if (numApplied > 0) {
            if (SPlanRewriteRule.LOG.isDebugEnabled)
                SPlanRewriteRule.LOG.debug("RewritePullAggAboveMult (num=$numApplied) on mult ${mult.id}. Top: ${top.id} $top")
            return RewriteResult.NewNode(top)
        }
        return RewriteResult.NoChange
    }

}

package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.Hop.AggOp
import org.apache.sysml.hops.spoof2.plan.*
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
 *
 * Later, we will add the following functionality.
 * Requires providing fresh names for the agg +.
 * <pre>
 *      \ /    ->     \ /
 *       *     ->      +
 *     // \    ->      |
 *    +    ..  ->      *
 * \ /         -> \ // | \
 *  C          ->  C  .. ..
 * </pre>
 *
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
                    && agg.parents.size == 1 //agg.parents.all { it == mult } // this is incorrect if aggChild is an SNodeAggregate (or SNodeBind?); need to make fresh names
                    && agg.op == AggOp.SUM ) {
                val numAggInMultInput = agg.parents.count() // add aggChild to mult.inputs numAggInMultInput times
                val aggChild = agg.inputs[0]

                val iAggChildToAgg = aggChild.parents.indexOf(agg)
                aggChild.parents[iAggChildToAgg] = mult
                repeat(numAggInMultInput-1) {
                    aggChild.parents.add(mult)
                }
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
                mult.inputs[iMultToAgg] = aggChild // replace with the following when we are ready to provide fresh names.
//                mult.inputs.mapInPlace {
//                    if( it == agg ) aggChild
//                    else it
//                }
                mult.parents.clear()
                mult.parents.add(agg)
                //
                mult.refreshSchema()
                agg.refreshSchema()
                if( top === node ) // original parents connect to the first pulled aggregate
                    top = agg      // a later rewrite rule will combine consecutive aggregates
                numApplied += numAggInMultInput
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

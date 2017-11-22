package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.Hop.AggOp
import org.apache.sysml.hops.spoof2.plan.mapInPlace
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.plan.SNodeNary.NaryOp

/**
 * Pattern:
 * ```
 *      \ /    ->    \ /
 *       *     ->     Σ
 *     / | \   ->     |
 *    Σ  .. .. ->     *
 * \ /         -> \ / | \
 *  C          ->  C  .. ..
 * ```
 * and no foreign parents on Σ.
 *
 * Illustrated above is the "no other parents on Σ" case.
 * Illustrated below is the "Σ has multiple parents, all of which are the *" case.
 *
 * Common Subexpression Splitting:
 * Copies the CSE and provides fresh names for the aggregated names.
 * ```
 *      \ /    ->   \ /
 *       *     ->    Σ[a,a']
 *     // \    ->    |
 * F  Σ[a] ..  -> F  *
 * \ /         -> \ /|         \
 *  C          ->  C C'[a->a'] ..
 * ```
 *
 * This is a tricky situation.
 * ```
 *      \ /    ->            \ /
 *       *     ->             Σ[a']
 *     /  \    ->             |
 * F  Σ[a] D[a]->  F          *
 * \ /         ->  |         / \
 *  C          ->  C C'[a->a'] D[a]
 * ```
 *
 * ```
 *      \ /    ->          \ /
 *       *     ->           Σ[a']
 *     /  \    ->           |
 *    Σ[a] D[a]->           *      (Σ[a] stripped)
 *     \  /    ->          / \
 *      C      ->  C'[a->a'] D[a]
 *             ->              |
 *             ->              C
 * ```
 *
 * Due to RewriteSplitCSE:
 * ```
 *      \ /    ->          \ /
 *  F    *     ->           Σ[a']
 *   \ /  \    ->           |
 *    Σ[a] D[a]->           *       F
 *     \  /    ->          / \      |
 *      C      ->   C'[a->a'] D[a]  Σ[a]
 *             ->               \  /
 *             ->                C
 * ```
 */
class RewritePullAggAboveMult : SPlanRewriteRule() {

    override fun rewriteNode(parent: SNode, node: SNode, inputPosition: Int): RewriteResult {
        if( node !is SNodeNary || node.op != NaryOp.MULT ) // todo generalize to other * functions that are semiring to +
            return RewriteResult.NoChange
        val mult: SNodeNary = node
        var top: SNode = mult
        var numApplied = 0

        for (iMultToAgg in mult.inputs.indices) { // index of agg in mult
            var agg = mult.inputs[iMultToAgg]
            if( agg is SNodeAggregate
                    && agg.parents.all { it == mult }
                    && agg.op == AggOp.SUM ) {
                val numAggInMultInput = agg.parents.count() // this is >1 if the mult has a CSE
                if (SPlanRewriteRule.LOG.isDebugEnabled && numAggInMultInput > 1)
                    SPlanRewriteRule.LOG.debug("In RewritePullAggAboveMult, splitting CSE (${agg.id}) $agg " +
                            "that occurs $numAggInMultInput times as input to (${mult.id}) $mult")

                val (overlapAggNames, nonOverlapAggNames) = agg.aggs.partition { n, _ -> n in mult.schema }
                if( overlapAggNames.isNotEmpty() ) {
                    if( nonOverlapAggNames.isNotEmpty() ) {
                        // split agg into agg and aggDown. aggDown contains the non-overlapping agg names.
                        agg.inputs[0].parents.remove(agg)
                        val aggDown = SNodeAggregate(agg.op, agg.inputs[0], nonOverlapAggNames)
                        aggDown.parents += agg
                        agg.aggs -= nonOverlapAggNames
                        agg.inputs[0] = aggDown
                        if (SPlanRewriteRule.LOG.isDebugEnabled)
                            SPlanRewriteRule.LOG.debug("In RewritePullAggAboveMult, " +
                                    "split (${agg.id}) $agg into $overlapAggNames and $nonOverlapAggNames")
                    }
                    val newAgg = agg.copyAggRenameDown()
                    repeat(numAggInMultInput) {
                        newAgg.parents += mult
                    }
                    mult.inputs.mapInPlace {
                        if( agg in it.parents )
                            it.parents.remove(agg)
                        if( it == agg ) newAgg
                        else it
                    }

                    // Dead code elim, if agg has only one parent (mult)
                    agg.parents.remove(mult)
                    if( agg.parents.isEmpty() )
                        stripDead(agg)

                    if (SPlanRewriteRule.LOG.isDebugEnabled)
                        SPlanRewriteRule.LOG.debug("In RewritePullAggAboveMult, " +
                                "copy (${agg.id}) $agg to renamed id=${newAgg.id} $newAgg")
                    mult.refreshSchemasUpward()
                    agg = newAgg
                }

                for( multInputIdx in iMultToAgg+1 until mult.inputs.size) {
                    if( mult.inputs[multInputIdx] == agg ) {
                        val newAgg = agg.copyAggRenameDown()
                        agg.aggs += newAgg.aggs
                        newAgg.inputs[0].parents[0] = mult
                        mult.inputs[multInputIdx] = newAgg.inputs[0]
                    }
                }

                val aggChild = agg.inputs[0]
                aggChild.parents[aggChild.parents.indexOf(agg)] = mult
                agg.inputs[0] = mult
                agg.parents.clear()
                agg.parents += mult.parents
                // set mult.parents to agg
                mult.parents.forEach { multParent ->
                    for (iMultParentToMult in multParent.inputs.indices) {
                        if( multParent.inputs[iMultParentToMult] == mult )
                            multParent.inputs[iMultParentToMult] = agg
                    }
                }

                mult.inputs[iMultToAgg] = aggChild
                mult.parents.clear()
                mult.parents += agg
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

    companion object {
        private fun stripDead(node: SNode) {
            val sb: StringBuilder?
            val action: (SNode) -> Unit
            if (SPlanRewriteRule.LOG.isDebugEnabled) {
                sb = StringBuilder()
                action = {sb.append(',').append(it.id)}
            } else {
                sb = null
                action = {}
            }
            stripDead(node, action)
            if (SPlanRewriteRule.LOG.isDebugEnabled) {
                val s = sb!!.substring(1).toString()
                SPlanRewriteRule.LOG.debug("In RewritePullAggAboveMult, dead code eliminate $s")
            }
        }
        private fun stripDead(node: SNode, action: (SNode) -> Unit) {
            node.parents.removeIf { it.parents.isEmpty() }
            if (node.parents.isEmpty()) {
                action(node)
                node.inputs.forEach { stripDead(it, action) }
            }
        }
    }
}

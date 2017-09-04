package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.Hop.AggOp
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.plan.SNodeNary.NaryOp

/**
 * Pattern:
 * ```
 *      \ /    ->        \ /
 *       *     ->         +
 *     / | \   ->       /  \
 *    +  D  E  ->     *     *
 * \ / \       -> \ / | \ / | \
 *  C1  C2     ->  C1 D  E  D  C2
 * ```
 * and no foreign parents on +. (D and E are shared.)
 */
class RewritePullPlusAboveMult : SPlanRewriteRule() {

    override fun rewriteNode(parent: SNode, node: SNode, inputPosition: Int): RewriteResult {
        if( node !is SNodeNary || node.op != NaryOp.MULT ) // todo generalize to other * functions that are semiring to +
            return RewriteResult.NoChange
        val mult: SNodeNary = node
        val plus = mult.inputs.find {
            it is SNodeNary && it.op == SNodeNary.NaryOp.PLUS && it.parents.size == 1
        } ?: return RewriteResult.NoChange
        val multInputs = ArrayList(mult.inputs)
        val multToPlus = multInputs.indexOf(plus)
        val plusInputs = ArrayList(plus.inputs)
        plusInputs.forEach { it.parents.remove(plus) }
        plus.inputs.clear()

        mult.parents.forEach { it.inputs[it.inputs.indexOf(mult)] = plus }
        plus.parents.clear()
        plus.parents += mult.parents
        mult.parents.clear()

        plus.inputs += mult
        mult.parents += plus
        mult.inputs[multToPlus] = plusInputs[0]
        plusInputs[0].parents += mult
        mult.refreshSchema()

        for (i in 1..plusInputs.size-1) {
            multInputs[multToPlus] = plusInputs[i]
            val m = SNodeNary(NaryOp.MULT, multInputs)
            plus.inputs += m
            m.parents += plus
        }
        plus.refreshSchema()

        if (SPlanRewriteRule.LOG.isDebugEnabled)
            SPlanRewriteRule.LOG.debug("RewritePullPlusAboveMult on mult ${mult.id} and plus ${plus.id}")
        return RewriteResult.NewNode(plus)
    }

}

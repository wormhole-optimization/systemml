package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.SNodeNary

/**
 * Split Nary multiply ops that have >2 inputs into a chain of multiplies.
 * Uses the order of the inputs to the multiply. Does not determine a new order.
 * If the order of the inputs is *bad*, then the result may not be compilable into a Hop Dag (because it creates tensor intermediaries).
 *
 * Requires [RewriteMultiplyCSEToPower], which rewrites common subexpressions of the multiply to unary powers.
 */
class RewriteSplitMultiply : SPlanRewriteRule() {

    override fun rewriteNode(parent: SNode, node: SNode, pos: Int): SNode {
        val origInputSize = node.inputs.size
        if( node is SNodeNary && node.op == SNodeNary.NaryOp.MULT && origInputSize > 2 ) { // todo generalize to other * functions
            val curMult = node
            // todo check sublist
            val inputParentIndexes = curMult.inputs.map { it.parents.indexOf(curMult) }
            rSplitMultiply(curMult, inputParentIndexes)

            if (SPlanRewriteRule.LOG.isDebugEnabled)
                SPlanRewriteRule.LOG.debug("RewriteSplitMultiply (num=${origInputSize-2}) onto top ${curMult.id} $curMult.")
        }
        return node
    }

    private tailrec fun rSplitMultiply(curMult: SNodeNary, inputParentIndexes: List<Int>) {
        val curSize = curMult.inputs.size
        if( curSize == 2 ) {
            curMult.inputs.forEachIndexed { i, cmi ->
                cmi.parents[inputParentIndexes[i]] = curMult
            }
            return
        }
        val firstInput = curMult.inputs[0]
        firstInput.parents[inputParentIndexes[0]] = curMult
        val nextMult = SNodeNary(curMult.op, curMult.inputs.subList(1, curSize))
        curMult.inputs.clear()
        curMult.inputs += firstInput
        curMult.inputs += nextMult
        nextMult.parents += curMult
        rSplitMultiply(nextMult, inputParentIndexes.drop(1))
    }

}

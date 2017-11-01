package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.spoof2.plan.*

/**
 * Split Nary multiply ops that have >2 inputs into a chain of multiplies.
 * Uses the order of the inputs to the multiply. Does not determine a new order.
 * If the order of the inputs is *bad*, then the result may not be compilable into a Hop Dag (because it creates tensor intermediaries).
 *
 * Requires [RewriteMultiplyCSEToPower], which rewrites common subexpressions of the multiply to unary powers.
 */
class RewriteSplitMultiplyPlus : SPlanRewriteRule() {

    override fun rewriteNode(parent: SNode, node: SNode, inputPosition: Int): RewriteResult {
        val origInputSize = node.inputs.size
        if( node is SNodeNary
                && (node.op == SNodeNary.NaryOp.MULT || node.op == SNodeNary.NaryOp.PLUS)
                && origInputSize > 2 ) { // todo generalize to other * functions
            val curMult = node

            adjustInputOrder(curMult)
            splitMultiply(curMult)

            if (LOG.isDebugEnabled)
                LOG.debug("RewriteSplitMultiplyPlus (num=${origInputSize-2}) onto top ${curMult.id} $curMult.")
            return RewriteResult.NewNode(curMult)
        }
        return RewriteResult.NoChange
    }

    companion object {

        /**
         * Change the order of inputs to mult so as to enable Hop reconstruction.
         * May affect schema.
         */
        private fun adjustInputOrder(mult: SNodeNary) {
            if (mult.parents.size == 1 && mult.parents[0] is SNodeAggregate) {
                val parent = mult.parents[0] as SNodeAggregate
                // heuristic: the first inputs to multiply should be the ones with the most things to aggregate.
                mult.inputs.sortWith(
                        (compareBy<SNode> { parent.aggs.names.intersect(it.schema.names).count() })
                                .thenComparing<Int> { -(it.schema.names - parent.aggs).size }
                )
                val changed = mult.refreshSchemasUpward()
                if (changed && LOG.isDebugEnabled)
                    LOG.debug("In RewriteSplitMultiplyPlus, reorder inputs of $mult id=${mult.id} to schema ${mult.schema}.")
            }
        }

        internal fun splitMultiply(mult: SNodeNary) {
            rSplitMultiply(mult, mult)
        }

        private tailrec fun rSplitMultiply(curMult: SNodeNary, origMult: SNodeNary) {
            val curSize = curMult.inputs.size
            if (curSize == 2) {
                curMult.inputs.forEach { it.parents[it.parents.indexOf(origMult)] = curMult }
                return
            }
            val firstInput = curMult.inputs[0]
            firstInput.parents[firstInput.parents.indexOf(origMult)] = curMult
            val otherInputs = curMult.inputs.subList(1, curSize)
            val nextMult = SNodeNary(curMult.op, otherInputs)  // this adds nextMult as parent to otherInputs
            otherInputs.forEach { child ->
                // but we will replace the existing parent origMult later
                child.parents.removeAt(child.parents.size - 1)
            }
            curMult.inputs.clear()
            curMult.inputs += firstInput
            curMult.inputs += nextMult
            nextMult.parents += curMult
            rSplitMultiply(nextMult, origMult)
        }

    }

}

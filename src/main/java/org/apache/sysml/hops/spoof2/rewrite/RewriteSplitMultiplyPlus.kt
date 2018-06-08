package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.LiteralOp
import org.apache.sysml.hops.spoof2.plan.*

/**
 * Split Nary multiply ops that have >2 inputs into a chain of multiplies.
 * Uses the order of the inputs to the multiply. Does not determine a new order.
 * If the order of the inputs is *bad*, then the result may not be compilable into a Hop Dag (because it creates tensor intermediaries).
 *
 * Requires [RewriteMultiplyCSEToPower], which rewrites common subexpressions of the multiply to unary powers.
 */
class RewriteSplitMultiplyPlus : SPlanRewriteRule() {

    override fun rewriteNode(parent: SNode, node: SNode, inputPosition: Int, allRoots: List<SNode>): RewriteResult {
        val origInputSize = node.inputs.size
        if( node is SNodeNary
                && (node.op == SNodeNary.NaryOp.MULT || node.op == SNodeNary.NaryOp.PLUS)
                && origInputSize > 2 ) { // todo generalize to other * functions

            adjustInputOrder(node)
            combineCommon(node)
            splitMultiply(node)

            if (LOG.isDebugEnabled)
                LOG.debug("RewriteSplitMultiplyPlus (num=${origInputSize-2}) onto top ${node.id} $node.")
            return RewriteResult.NewNode(node)
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


                val aggsToDeg = parent.aggs.keys.map { a ->
                    a to mult.inputs.filter { a in it.schema }.flatMap { it.schema.keys }.toSet().size - 1
                }
                val priorityAggs = aggsToDeg.sortedBy { it.second }

                // re-order inputs such that aggregates can be pushed down, using the degree of each aggregated name
                mult.inputs.sortWith( compareBy<SNode> {
                    it.schema.keys.map { n -> priorityAggs.find { it.first == n }?.second?.times(-1) ?: Int.MIN_VALUE  }.max() ?: Int.MIN_VALUE
                } )

                val changed = mult.refreshSchemasUpward()
                if (changed && LOG.isDebugEnabled)
                    LOG.debug("In RewriteSplitMultiplyPlus, reorder inputs of $mult id=${mult.id} to schema ${mult.schema}.")
            }
        }

        // todo merge this into RewriteMultiplyCSEToPower
        private fun combineCommon(mult: SNodeNary) {
            val inputs = mult.inputs.distinct()
            if( inputs.size == mult.inputs.size )
                return
            inputs.forEach { input ->
                val cnt = mult.inputs.count { it == input }
                if( cnt > 1 ) {
                    val pos = mult.inputs.indexOf(input)
                    mult.inputs.removeIf { it == input }
                    input.parents.removeIf { it == mult }
                    val powOp = when(mult.op) {
                        SNodeNary.NaryOp.MULT -> SNodeNary.NaryOp.POW
                        SNodeNary.NaryOp.PLUS -> SNodeNary.NaryOp.MULT
                        else -> throw UnsupportedOperationException("don't know how to handle op ${mult.op}")
                    }
                    val lit = SNodeData(LiteralOp(cnt.toLong()))
                    val pow = SNodeNary(powOp, input, lit)
                    mult.inputs.add(pos, pow)
                    pow.parents += mult
                    if( LOG.isTraceEnabled )
                        LOG.trace("RewriteSplitMultiplyPlus: combine repeated inputs ${inputs.map { it.id }} on (${mult.id}) $mult")
                }
            }
        }

        internal fun splitMultiply(mult: SNodeNary) {
            rSplitMultiply(mult, mult)
        }

        private tailrec fun rSplitMultiply(curMult: SNodeNary, origMult: SNodeNary) {
            val curSize = curMult.inputs.size
            if (curSize == 2) {
                // There is some problem when the mult has repeated inputs with this next line's "indexOf".
                // combineCommon replaces repeated inputs, as well as RewriteMultiplyCSEToPower
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

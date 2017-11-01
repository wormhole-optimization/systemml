package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.LiteralOp
import org.apache.sysml.hops.spoof2.plan.*

/**
 * Rewrite +s whose inputs contain a *(-1) into a -.
 * If need be, converts a*(-1) + b*(-1) into 0 - (a + b).
 *
 * Simplifies -1 multiply chains, as in `(-1)*(-1)*(-1) = -1`.
 */
class RewriteRecoverMinus : SPlanRewriteRule() {

    override fun rewriteNode(parent: SNode, node: SNode, inputPosition: Int): RewriteResult {
        if( node is SNodeNary
                && (node.op == SNodeNary.NaryOp.PLUS) ) {
            val minus = separateMinus(node)
            if( minus !== node )
                return RewriteResult.NewNode(minus)
        }
        return RewriteResult.NoChange
    }

    companion object {
        private fun isNegOne(lit: SNode) = lit is SNodeData && lit.isLiteralNumeric && lit.literalDouble == -1.0

        private fun separateMinus(plus: SNodeNary): SNodeNary {
            if (plus.op == SNodeNary.NaryOp.PLUS) {
                // gather all inputs that are multiplied by -1 and have only this as parent
                // todo make more aggressive by considering parents that are all +s
                plus.inputs.mapInPlace { if (it is SNodeNary) simplifyMultNegOne(it) else it }

                val multByNegOnes = plus.inputs.filter { pi ->
                    pi is SNodeNary && pi.op == SNodeNary.NaryOp.MULT
                            && pi.inputs.count { isNegOne(it) } == 1
                            && pi.parents.all { it == plus }
                }
                if (multByNegOnes.isNotEmpty()) {
                    // structure:
                    //       -
                    //    +    +
                    //   P..  N..
                    // move multByNegOne from plus to a new plus
                    multByNegOnes.forEach {
                        // all parents are plus
                        it.parents -= plus; plus.inputs -= it
                    }
                    multByNegOnes.distinct().forEach {
                        // elim -1
                        val negOne = it.inputs.find { isNegOne(it) }!!
                        negOne.parents -= it
                        it.inputs -= negOne
                    }
                    val plusNegative = SNodeNary(SNodeNary.NaryOp.PLUS, multByNegOnes)
                    // eliminate mult if singleton
                    multByNegOnes.distinct().forEach {
                        if (it.inputs.size == 1) {
                            it.parents.removeIf { pa -> pa == plusNegative }
                            plusNegative.inputs.mapInPlace { pni ->
                                if (pni == it) it.inputs[0]
                                else pni
                            }
                            it.inputs[0].parents.mapInPlace { below ->
                                if (below == it) plusNegative
                                else below
                            }
                        }
                    }
                    val parents = ArrayList(plus.parents)
                    plus.parents.clear()
                    val minus = SNodeNary(SNodeNary.NaryOp.MINUS, plus, plusNegative)
                    parents.forEach { it.inputs[it.inputs.indexOf(plus)] = minus; minus.parents += it }

                    // if plusNegative has 1 input, eliminate it
                    if( plusNegative.inputs.size == 1 ) {
                        minus.inputs[1] = plusNegative.inputs[0]
                        plusNegative.parents -= minus
                        plusNegative.inputs[0].parents -= plusNegative
                        plusNegative.inputs[0].parents += minus
                    }

                    // if plus has 0 inputs, create a constant 0.
                    if( plus.inputs.isEmpty() ) {
                        val zero = SNodeData(LiteralOp(0.0))
                        plus.inputs += zero
                        zero.parents += plus
                    }
                    // if plus has 1 input, eliminate it
                    if( plus.inputs.size == 1 ) {
                        minus.inputs[0] = plus.inputs[0]
                        plus.parents -= minus
                        plus.inputs[0].parents -= plus
                        plus.inputs[0].parents += minus
                    }

                    if (LOG.isTraceEnabled)
                        LOG.trace("RewriteSplitMultiplyPlus: split negative added terms from (${plus.id}) into a minus (${minus.id})")
                    return minus
                }
            }
            return plus
        }

        /**
         * Remove -1 * -1
         */
        private fun simplifyMultNegOne(mult: SNodeNary): SNode {
            if (mult.op == SNodeNary.NaryOp.MULT) {
                var idxNegOne = -1
                var idx = 0
                while (idx < mult.inputs.size) {
                    val input = mult.inputs[idx]
                    if (input is SNodeData && input.isLiteralNumeric && input.literalDouble == -1.0) {
                        if (idxNegOne < 0) {
                            idxNegOne = idx
                        } else {
                            assert(idx != idxNegOne)
                            // remove idx and idxNegOne
                            mult.inputs.removeAt(idx)
                            input.parents -= mult
                            val other = mult.inputs[idxNegOne]
                            mult.inputs.removeAt(idxNegOne)
                            other.parents -= mult
                            if (LOG.isTraceEnabled)
                                LOG.trace("RewriteSplitMultiplyPlus: eliminate -1 * -1 as (${other.id}) * (${input.id}) underneath a +")
                            idxNegOne = -2
                            idx--
                        }
                    }
                    idx++
                }
                if (mult.inputs.size == 1) {
                    mult.parents.forEach { it.inputs[it.inputs.indexOf(mult)] = mult.inputs[0]; mult.inputs[0].parents += it }
                    mult.parents.clear()
                    mult.inputs[0].parents -= mult
                    return mult.inputs[0]
                }
            }
            return mult
        }
    }
}
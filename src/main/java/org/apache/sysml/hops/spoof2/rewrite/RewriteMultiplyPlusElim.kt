package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.SNodeNary

/**
 * Combine consecutive multiplies into one.
 * Handles common subexpresions, when multiple inputs are the same expression (and that expression has no other parents).
 */
class RewriteMultiplyPlusElim : SPlanRewriteRule() {

    override fun rewriteNode(parent: SNode, node: SNode, inputPosition: Int): RewriteResult {
        if( node is SNodeNary &&
                (node.op == SNodeNary.NaryOp.MULT || node.op == SNodeNary.NaryOp.PLUS)
                ) { // todo generalize to other * functions
            val mult1 = node
            var i1to2 = 0
            var numApplied = 0
            while( i1to2 < mult1.inputs.size ) {
                val mult2 = mult1.inputs[i1to2]
                if( mult2 !is SNodeNary || mult2.op != mult1.op || mult2.parents.any { it !== mult1 } ) {
                    i1to2++
                    continue
                }
                // all of mult2's parents are exactly mult1
                // each time mult2 occurs as an input to mult1, we need to add mult1's children in the place of mult2
                val i1to2all = mult1.inputs.indices.filter { mult1.inputs[it] === mult2 }
                i1to2 = i1to2all.first() // reset to index of first occurrence of this mult2 in mult1.inputs
                val newMult1Inputs = ArrayList<SNode>(mult1.inputs.size - i1to2all.size + i1to2all.size * mult2.inputs.size)

                // first occurrence of mult2
                newMult1Inputs.addAll(mult1.inputs.subList(0, i1to2))
                // for each of mult2's inputs, change its parent to mult1 and add it to the newMult1Inputs
                mult2.inputs.forEach { mult2input ->
                    val i3to2 = mult2input.parents.indexOf(mult2)
                    mult2input.parents[i3to2] = mult1
                }
                newMult1Inputs.addAll(mult2.inputs)
                var ilast = i1to2

                // additional occurrences of mult2
                for (i12 in i1to2all.drop(1)) {
                    newMult1Inputs.addAll(mult1.inputs.subList(ilast + 1, i12))
                    newMult1Inputs.addAll(mult2.inputs)
                    mult2.inputs.forEach { mult2input ->
                        mult2input.parents.add(mult1) // new parent!
                    }
                    ilast = i12
                }

                // remaining inputs to mult1
                newMult1Inputs.addAll(mult1.inputs.subList(ilast + 1, mult1.inputs.size))

                // assign to mult1
                mult1.inputs.clear()
                mult1.inputs.addAll(newMult1Inputs)
                // don't skip the added children; they could also be multiplies
                numApplied += i1to2all.size
            }

            if (numApplied > 0) {
                if (SPlanRewriteRule.LOG.isDebugEnabled)
                    SPlanRewriteRule.LOG.debug("RewriteMultiplyPlusElim (num=$numApplied) onto top ${mult1.id} $mult1.")
                return RewriteResult.NewNode(mult1)
            }
        }
        return RewriteResult.NoChange
    }

}

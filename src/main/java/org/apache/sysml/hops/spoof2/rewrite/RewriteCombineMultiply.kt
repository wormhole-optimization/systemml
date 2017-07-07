package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.SNodeNary

/**
 * Combine consecutive multiplies into one.
 */
class RewriteCombineMultiply : SPlanRewriteRule() {

    override fun rewriteNode(parent: SNode, node: SNode, pos: Int): SNode {
        if( node is SNodeNary && node.op == SNodeNary.NaryOp.MULT ) { // todo generalize to other * functions
            val mult1 = node
            var i1to2 = 0
            var numApplied = 0
            while( i1to2 < mult1.inputs.size ) {            // Todo handle case where an input has other parents
                val mult2 = mult1.inputs[i1to2]      // Todo handle created 3-way n-ary multiplies
                if( mult2 is SNodeNary && mult2.op == mult1.op ) {
                    val newMult1Inputs = ArrayList<SNode>(mult1.inputs.size-1+mult2.inputs.size)
                    newMult1Inputs.addAll(mult1.inputs.subList(0,i1to2))
                    // for each of mult2's inputs, change its parent to mult1 and add it to the newMult1Inputs
                    mult2.inputs.forEach { mult2input ->
                        val i3to2 = mult2input.parents.indexOf(mult2)
                        mult2input.parents[i3to2] = mult1
                    }
                    newMult1Inputs.addAll(mult2.inputs)
                    newMult1Inputs.addAll(mult1.inputs.subList(i1to2+1,mult1.inputs.size))
                    mult1.inputs.clear()
                    mult1.inputs.addAll(newMult1Inputs)
                    // don't skip the added children; they could also be multiples
//                    i1to2 += mult2.inputs.size
                    numApplied++
                }
                else i1to2++
            }
            if (numApplied > 0 && SPlanRewriteRule.LOG.isDebugEnabled)
                SPlanRewriteRule.LOG.debug("RewriteCombineMultiply (num=$numApplied) onto top ${mult1.id} $mult1.")
        }
        return node
    }

}

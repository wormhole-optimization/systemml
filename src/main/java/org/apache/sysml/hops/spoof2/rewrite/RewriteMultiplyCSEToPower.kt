package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.LiteralOp
import org.apache.sysml.hops.rewrite.HopRewriteUtils
import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.SNodeData
import org.apache.sysml.hops.spoof2.plan.SNodeNary

/**
 * When a multiply has common subexpression inputs, rewrite them as a power.
 * Combine their parents together.
 */
class RewriteMultiplyCSEToPower : SPlanRewriteRule() {

    override fun rewriteNode(parent: SNode, node: SNode, pos: Int): RewriteResult {
        if( node is SNodeNary && node.op == SNodeNary.NaryOp.MULT ) { // todo generalize to other * functions - min and max don't change input, + doubles input
            var numCSEs = 0
            var multToChild = 0
            while (multToChild < node.inputs.size) {
                val child = node.inputs[multToChild]
                val numInstancesOfChild = node.inputs.count { it == child }
                if( numInstancesOfChild > 1 ) {
                    node.inputs.removeIf { it == child }
                    // remove all instances in parents of child
                    child.parents.removeIf { it == node }
                    val pow = SNodeNary(SNodeNary.NaryOp.POW, child, SNodeData(LiteralOp(numInstancesOfChild.toLong())))
                    node.inputs.add(multToChild, pow)
                    pow.parents += node
                    if (SPlanRewriteRule.LOG.isDebugEnabled)
                        SPlanRewriteRule.LOG.debug("RewriteMultiplyCSEToPower on multiply $node id=${node.id}, " +
                                "merged $numInstancesOfChild common subexpressions of $child id=${child.id} into power $pow id=${pow.id}.")
                    numCSEs++
                }
                multToChild++
            }
            if( numCSEs > 0 )
                return RewriteResult.NewNode(node)
        }
        return RewriteResult.NoChange
    }

}

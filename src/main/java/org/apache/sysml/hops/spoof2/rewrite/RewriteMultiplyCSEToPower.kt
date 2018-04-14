package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.LiteralOp
import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.SNodeData
import org.apache.sysml.hops.spoof2.plan.SNodeNary
import org.apache.sysml.hops.spoof2.plan.stripDead

/**
 * When a multiply has common subexpression inputs, rewrite them as a power.
 * Combine their parents together.
 * Depends on common subexpression elimination.
 *
 * Also combine together children with their powers, when the power does not have foreign parents.
 */
class RewriteMultiplyCSEToPower : SPlanRewriteRule() {

    private fun SNode.isChildPower(node: SNode, child: SNode): Boolean {
        return this is SNodeNary && this.op == SNodeNary.NaryOp.POW
                && this.inputs[1] is SNodeData && ((this.inputs[1]) as SNodeData).isLiteral
                && node in this.parents && child == this.inputs[0]
                && this.parents.size == 1
    }

    override fun rewriteNode(parent: SNode, node: SNode, inputPosition: Int, allRoots: List<SNode>): RewriteResult {
        if( node is SNodeNary && node.op == SNodeNary.NaryOp.MULT ) { // todo generalize to other * functions - min and max don't change input, + doubles input
            var numCSEs = 0
            var multToChild = 0
            while (multToChild < node.inputs.size) {
                val child = node.inputs[multToChild]
                val numInstancesOfChild = node.inputs.count { it == child }
                // We can have floating-point powers
                val powerCountOfChild = node.inputs.sumByDouble { if (it.isChildPower(node, child)) (it.inputs[1] as SNodeData).literalDouble else 0.0 }
                if( numInstancesOfChild + powerCountOfChild > 1 ) {
                    node.inputs.removeIf {
                        if (it.isChildPower(node, child)) {
                            it.parents -= node
                            stripDead(it)
                            true
                        } else it == child
                    }
                    multToChild = Math.min(multToChild, node.inputs.size)
                    // remove all instances in parents of child
                    child.parents.removeIf { it == node || it.isChildPower(node, child) }
                    val pow = SNodeNary(SNodeNary.NaryOp.POW, child, SNodeData(LiteralOp(numInstancesOfChild + powerCountOfChild)))
                    node.inputs.add(multToChild, pow)
                    pow.parents += node
                    if (SPlanRewriteRule.LOG.isDebugEnabled)
                        SPlanRewriteRule.LOG.debug("RewriteMultiplyCSEToPower on multiply $node id=${node.id}, " +
                                "merged common subexpressions of $child id=${child.id} into power $pow id=${pow.id} with exponent ${numInstancesOfChild + powerCountOfChild}.")
                    numCSEs++
                }
                multToChild++
            }
            //eliminate unary mult
            if( node.inputs.size == 1 ) {
                val child = node.inputs[0]
                SNodeRewriteUtils.removeAllChildReferences(node) // clear node.inputs, child.parents
                SNodeRewriteUtils.rewireAllParentChildReferences(node, child) // for each parent of node, change its input from node to child and add the parent to child
                if (SPlanRewriteRule.LOG.isDebugEnabled)
                    SPlanRewriteRule.LOG.debug("RewriteMultiplyCSEToPower eliminate now-single-input multiply $node id=${node.id} whose child is $child id=${child.id}")
                return RewriteResult.NewNode(child)
            }
            if( numCSEs > 0 )
                return RewriteResult.NewNode(node)
        }
        return RewriteResult.NoChange
    }

}

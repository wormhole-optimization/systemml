package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.LiteralOp
import org.apache.sysml.hops.spoof2.plan.*

/**
 * Split common subexpressions when they would block a sum-product rearrangement.
 */
class RewriteSplitCSE : SPlanRewriteRule() {

    override fun rewriteNode(parent: SNode, node: SNode, pos: Int): RewriteResult {
        var numCSEsplits = 0
        if( node.parents.size > 1 ) {

            // Pull agg above multiply; combine agg
            if( node is SNodeAggregate && node.op == Hop.AggOp.SUM ) {
                val PRED: (SNode) -> Boolean = {
                    it is SNodeNary && it.op == SNodeNary.NaryOp.MULT
                    || it is SNodeAggregate && it.op == node.op
                }
                while( node.parents.size > 1 && node.parents.any(PRED)  ) {
                    val multParent = node.parents.first(PRED)

                    val copy = SNodeAggregate(node.op, node.input, node.aggreateNames)

                    multParent.inputs[multParent.inputs.indexOf(node)] = copy
                    node.parents -= multParent
                    copy.parents += multParent
                    copy.visited = multParent.visited
                    numCSEsplits++
                }
            }
            // Combine *
            else if( node is SNodeNary && node.op == SNodeNary.NaryOp.MULT ) {
                val PRED: (SNode) -> Boolean = {
                    it is SNodeNary && it.op == SNodeNary.NaryOp.MULT
                }
                while( node.parents.size > 1 && node.parents.any(PRED)  ) {
                    val multParent = node.parents.first(PRED)

                    val copy = SNodeNary(node.op, node.inputs)

                    multParent.inputs[multParent.inputs.indexOf(node)] = copy
                    node.parents -= multParent
                    copy.parents += multParent
                    copy.visited = multParent.visited
                    numCSEsplits++
                }
            }

        }
        if (numCSEsplits > 0) {
            if (SPlanRewriteRule.LOG.isDebugEnabled)
                SPlanRewriteRule.LOG.debug("RewriteSplitCSE $numCSEsplits split CSEs on (${node.id}) $node")
            return RewriteResult.NewNode(node)
        }
        return RewriteResult.NoChange
    }

}

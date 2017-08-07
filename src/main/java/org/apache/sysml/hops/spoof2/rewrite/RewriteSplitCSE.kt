package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.spoof2.plan.*

/**
 * Split common subexpressions when they would block a sum-product rearrangement.
 *
 * *-Σ, Σ-Σ, *-*, *-+
 */
class RewriteSplitCSE : SPlanRewriteRule() {

    override fun rewriteNode(parent: SNode, node: SNode, pos: Int): RewriteResult {
        val ChildIdxFun: (IndexedValue<SNode>) -> SNode = { (i,child) ->
            val copy: SNode = child.shallowCopyNoParentsYesInputs()
            child.parents -= node
            node.inputs[i] = copy
            copy.parents += node
            copy
        }
        val FilterFun: (IndexedValue<SNode>) -> Boolean =
            // Pull agg above multiply; Combine *; Pull + above *
            if( node is SNodeNary && node.op == SNodeNary.NaryOp.MULT ) {
                { (_,it) ->
                    it.parents.size > 1 && (
                            it is SNodeNary && (it.op == SNodeNary.NaryOp.MULT || it.op == SNodeNary.NaryOp.PLUS)
                            || it is SNodeAggregate && it.op == Hop.AggOp.SUM )
                }
            }
            // combine agg
            else if( node is SNodeAggregate && node.op == Hop.AggOp.SUM ) {
                { (_,it):IndexedValue<SNode> ->
                    it.parents.size > 1 && (
                            it is SNodeAggregate && it.op == Hop.AggOp.SUM )
                } as (IndexedValue<SNode>) -> Boolean
            }
            else return RewriteResult.NoChange

        val numCSEsplits = node.inputs.withIndex().filter(FilterFun).map(ChildIdxFun).size
        if( numCSEsplits > 0 ) {
            if (SPlanRewriteRule.LOG.isDebugEnabled)
                SPlanRewriteRule.LOG.debug("RewriteSplitCSE $numCSEsplits split CSEs on (${node.id}) $node")
            return RewriteResult.NewNode(node)
        }
        return RewriteResult.NoChange
    }

}

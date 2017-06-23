package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.SNodeAggregate
import org.apache.sysml.hops.spoof2.plan.SNodeNary
import org.apache.sysml.hops.spoof2.plan.SNodeNary.NaryOp

class RewriteTransposeElimination : SPlanRewriteRule() {
    override fun rewriteNode(parent: SNode, node: SNode, pos: Int): SNode {
        if (node is SNodeAggregate && node.inputs[0] is SNodeNary
                && (node.inputs[0] as SNodeNary).op === NaryOp.TRANSPOSE) {
            val input = node.inputs[0]
            SNodeRewriteUtils.replaceChildReference(node, input,
                    input.inputs[0])

            SPlanRewriteRule.LOG.debug("Applied RewriteTransposeElimination.")
        }

        return node
    }

}

package org.apache.sysml.hops.spoof2.enu2

import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriteRule

/**
 *
 */
object RewriteNotNotElim : SPlanRewriteRule() {
    override fun rewriteNode(parent: SNode, node: SNode, inputPosition: Int, allRoots: List<SNode>): SPlanRewriteRule.RewriteResult {
        if (node is SNodeNary && node.op == SNodeNary.NaryOp.NOT) {
            val inp = node.inputs[0]
            if (inp is SNodeNary && inp.op == SNodeNary.NaryOp.NOT) {
                val below = inp.inputs[0]
                node.parents.toList().forEach { pa ->
                    pa.inputs[pa.inputs.indexOf(node)] = below
                    below.parents += pa
                    below.parents -= inp
                    node.parents -= pa
                }
                return SPlanRewriteRule.RewriteResult.NewNode(below)
            }
        }
        return SPlanRewriteRule.RewriteResult.NoChange
    }
}

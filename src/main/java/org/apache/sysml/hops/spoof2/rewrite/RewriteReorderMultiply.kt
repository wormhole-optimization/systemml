package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.spoof2.plan.*

/**
 * ```
           *
          / \
        a,b  *
            / \
         a,b   b,c
   to
           *
          / \
        b,c  *
            / \
         a,b  a,b
 * ```
 */
class RewriteReorderMultiply : SPlanRewriteRule() {
    override fun rewriteNode(parent: SNode, node: SNode, inputPosition: Int, allRoots: List<SNode>): RewriteResult {
        if (node is SNodeNary && node.op == SNodeNary.NaryOp.MULT) {
            val mult1 = node
            val mult2 = node.inputs.find { it is SNodeNary && it.op == SNodeNary.NaryOp.MULT }
            if (mult2 != null) {
                val otherIn1 = mult1.inputs.find { it !== mult2 }
                if (otherIn1 != null) {
                    val match2other = mult2.inputs.find { it.schema == otherIn1.schema }
                    if (match2other != null) {
                        val nomatch2 = mult2.inputs.find { it !== match2other && it.schema != otherIn1.schema }
                        if (nomatch2 != null) {
                            // swap otherIn1 with nomatch2
                            otherIn1.parents -= mult1
                            nomatch2.parents -= mult2
                            mult1.inputs[mult1.inputs.indexOf(otherIn1)] = nomatch2
                            mult2.inputs[mult2.inputs.indexOf(nomatch2)] = otherIn1
                            nomatch2.parents += mult1
                            otherIn1.parents += mult2
                            mult2.refreshSchema()
                            if (LOG.isTraceEnabled)
                                LOG.trace("RewriteReorderMultiply: at mult (${mult1.id}), switch input ($otherIn1) with input ($nomatch2) of child mult (${mult2.id})")
                            return RewriteResult.NewNode(node)
                        }
                    }
                }
            }
        }
        return RewriteResult.NoChange
    }
}
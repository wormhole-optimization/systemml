package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.LiteralOp
import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.SNodeData
import org.apache.sysml.hops.spoof2.plan.SNodeNary

/**
 * Subtract  + and *(-1);   ^2  Self-*
 * Handles common subexpresions, when multiple inputs are the same expression (and that expression has no other parents).
 */
class RewriteDecompose : SPlanRewriteRule() {

    override fun rewriteNode(parent: SNode, node: SNode, pos: Int): RewriteResult {
        if( node is SNodeNary && node.op == SNodeNary.NaryOp.MINUS ) {
            val left = node.inputs[0]
            val right = node.inputs[1]

            left.parents.remove(node)
            right.parents.remove(node)
            val mult = SNodeNary(SNodeNary.NaryOp.MULT, right, SNodeData(LiteralOp(-1)))
            val add = SNodeNary(SNodeNary.NaryOp.PLUS, left, mult)
            node.parents.forEach { it.inputs[it.inputs.indexOf(node)] = add; add.parents += it }

            if (SPlanRewriteRule.LOG.isDebugEnabled)
                SPlanRewriteRule.LOG.debug("RewriteDecompose subtract (${node.id}) into add (${add.id}) and multiply by -1.")
            return RewriteResult.NewNode(add)
        }
        else if( node is SNodeNary && node.op == SNodeNary.NaryOp.POW ) {
            val lit = node.inputs[1]
            if( lit is SNodeData && lit.isLiteral && lit.literalDouble == 2.0 ) { // todo more powers
                val left = node.inputs[0]

                left.parents.remove(node)
                lit.parents.remove(node)
                val mult = SNodeNary(SNodeNary.NaryOp.MULT, left, left)
                node.parents.forEach { it.inputs[it.inputs.indexOf(node)] = mult; mult.parents.add(it) }

                if (SPlanRewriteRule.LOG.isDebugEnabled)
                    SPlanRewriteRule.LOG.debug("RewriteDecompose ^2 (${node.id}) into self-multiply (${mult.id}).")
                return RewriteResult.NewNode(mult)
            }
        }
        return RewriteResult.NoChange
    }

}

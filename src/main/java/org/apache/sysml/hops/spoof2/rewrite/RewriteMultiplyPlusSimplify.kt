package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.rewrite.HopRewriteUtils
import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.SNodeData
import org.apache.sysml.hops.spoof2.plan.SNodeNary
import org.apache.sysml.hops.spoof2.plan.refreshSchemasUpward

/**
 * Combine consecutive multiplies into one.
 * Handles common subexpresions, when multiple inputs are the same expression (and that expression has no other parents).
 */
class RewriteMultiplyPlusSimplify : SPlanRewriteRule() {

    override fun rewriteNode(parent: SNode, node: SNode, inputPosition: Int): RewriteResult {
        if( node is SNodeNary &&
                (node.op == SNodeNary.NaryOp.MULT || node.op == SNodeNary.NaryOp.PLUS)
                ) {
            val zero = node.inputs.find { it is SNodeData && it.isLiteral && HopRewriteUtils.isLiteralOfValue(it.hop, 0.0) }
            if (zero != null) {
                when(node.op) {
                    SNodeNary.NaryOp.MULT -> { // multiply by 0
                        node.inputs.removeIf { it != zero && it.schema.isEmpty() }
                        // Disabled because it is bad to turn vectors/matrices into scalar 0
                        // todo replace with constant zero matrix with appropriate shape
//                        zero.parents.removeIf { it == node }
//                        node.parents.forEach { it.inputs[it.inputs.indexOf(node)] = zero; zero.parents += it }
//                        if( node.schema.isNotEmpty() )
//                            zero.parents.forEach { it.refreshSchemasUpward(node.schema.names.toSet()) }
                        if (LOG.isDebugEnabled)
                            LOG.debug("RewriteMultiplyPlusSimplify * by 0; elim (${node.id}) [kill attributes: ${node.schema.names}].")
                        return RewriteResult.NoChange // RewriteResult.NewNode(zero)
                    }
                    SNodeNary.NaryOp.PLUS -> { // add 0
                        zero.parents.removeIf { it == node }
                        node.inputs.removeIf { it == zero }
                        if( node.inputs.size == 1 ) {
                            val inp = node.inputs[0]
                            inp.parents -= node
                            node.parents.forEach { it.inputs[it.inputs.indexOf(node)] = inp; inp.parents += it }
                        }
                        if (LOG.isDebugEnabled)
                            LOG.debug("RewriteMultiplyPlusSimplify + with 0; remove 0 child (${zero.id}) from + (${node.id}).")
                        return RewriteResult.NewNode(node)
                    }
                    else -> throw AssertionError("unreachable")
                }
            }
        }
        return RewriteResult.NoChange
    }

}
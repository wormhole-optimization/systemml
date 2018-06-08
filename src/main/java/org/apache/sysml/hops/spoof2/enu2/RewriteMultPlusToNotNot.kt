package org.apache.sysml.hops.spoof2.enu2

import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriteRule

/**
 * Place a bind-unbind in between a *-+, in preparation for forming a DOGB.
 */
object RewriteMultPlusToNotNot : SPlanRewriteRule() {
    override fun rewriteNode(parent: SNode, node: SNode, inputPosition: Int, allRoots: List<SNode>): SPlanRewriteRule.RewriteResult {
        if (node is SNodeNary && node.op == SNodeNary.NaryOp.MULT) {
            var changed = false
            node.inputs.toSet().forEach { inp ->
                if (inp is SNodeNary && inp.op == SNodeNary.NaryOp.PLUS) {
//                    val map = inp.schema.toList().mapIndexed { i, n -> AU(i) to n.first as AB }.toMap()
                    val newinp = SNodeNary(SNodeNary.NaryOp.NOT, SNodeNary(SNodeNary.NaryOp.NOT, inp)) //SNodeBind(SNodeUnbind(inp, map), map)

                    if (SPlanRewriteRule.LOG.isDebugEnabled)
                        SPlanRewriteRule.LOG.debug("RewriteMultPlusToNotNot *-+ (${node.id}) $node - (${inp.id}) $inp. In between: (${newinp.id}) $newinp") // - (${newinp.input.id}) ${newinp.input}")

                    inp.parents.indices.reversed().forEach {paidx ->
                        val pa = inp.parents[paidx]
                        if (pa is SNodeNary && pa.op == SNodeNary.NaryOp.MULT) {
                            inp.parents.removeAt(paidx)
                            pa.inputs[pa.inputs.indexOf(inp)] = newinp
                            newinp.parents += pa
                            changed = true
                        }
                    }
                }
            }
            return if (changed) SPlanRewriteRule.RewriteResult.NewNode(node) else SPlanRewriteRule.RewriteResult.NoChange
        }
        return SPlanRewriteRule.RewriteResult.NoChange
    }
}

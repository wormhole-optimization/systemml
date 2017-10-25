package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.SPlanValidator
import org.apache.sysml.utils.Explain
import java.util.ArrayList

object SPlanTopDownRewriter {
    private const val CHECK_DURING_RECUSION = false
    private const val EXPLAIN_DURING_RECURSION = false

    fun rewriteDown(roots: List<SNode>, vararg rules: SPlanRewriteRule): Boolean =
            rewriteDown(roots, rules.asList())
    fun rewriteDown(roots: List<SNode>, rules: List<SPlanRewriteRule>): Boolean {
        SNode.resetVisited(roots)
        val changed = roots.fold(false) { changed, root -> rRewriteSPlan(root, rules, roots) || changed }
        SNode.resetVisited(roots)
        return changed
    }

    private fun rRewriteSPlan(node: SNode, rules: List<SPlanRewriteRule>, allRoots: List<SNode>): Boolean {
        if (node.visited)
            return false
        var changed = false

        for (i in node.inputs.indices) {
            var child = node.inputs[i]

            //apply actual rewrite rules
            for (r in rules) {
                val result = r.rewriteNode(node, child, i)
                when( result ) {
                    SPlanRewriteRule.RewriteResult.NoChange -> {}
                    is SPlanRewriteRule.RewriteResult.NewNode -> {
                        child = result.newNode
                        changed = true
                        if( CHECK_DURING_RECUSION )
                            SPlanValidator.validateSPlan(allRoots, false)
                        if( EXPLAIN_DURING_RECURSION && SPlanRewriteRule.LOG.isTraceEnabled )
                            SPlanRewriteRule.LOG.trace(Explain.explainSPlan(allRoots, true))
                    }
                }
            }

            //process children recursively after rewrites
            changed = rRewriteSPlan(child, rules, allRoots) || changed
        }

        node.visited = true
        return changed
    }
}
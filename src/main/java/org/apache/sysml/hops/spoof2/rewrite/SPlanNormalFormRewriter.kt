package org.apache.sysml.hops.spoof2.rewrite

import java.util.ArrayList

import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.SPlanValidator
import org.apache.sysml.utils.Explain

/**
 * 1. Apply the rewrite rules that get us into a normal form first, repeatedly until convergence.
 * 2. Apply RewriteNormalForm.
 * 3. Apply the rewrite rules that get us back to Hop-ready form, repeatedly until convergence.
 */
class SPlanNormalFormRewriter {
    private val _rulesToNormalForm = listOf(
            RewriteBindElim(),
            RewritePullAggAboveMult(),
            RewriteAggregateElim(),
            RewriteCombineMultiply()
    )
    private val _rulesNormalForm = listOf(
            RewriteMultiplyCSEToPower(),
            RewriteNormalForm()
    )
    private val _rulesToHopReady = listOf(
            RewriteSplitMultiply(),
            RewritePushAggIntoMult()
    )

    companion object {
        /** Whether to invoke the SPlanValidator after every rewrite pass. */
        internal const val CHECK = true
    }

    fun rewriteSPlan(roots: ArrayList<SNode>): ArrayList<SNode> {
        var count = 0
        do {
            if( CHECK )
                SPlanValidator.validateSPlan(roots)
            var changed = false
            SNode.resetVisited(roots)
            for (node in roots)
                changed = rRewriteSPlan(node, _rulesToNormalForm) || changed
            count++
        } while (changed)

        if( count == 1 ) {
            if( SPlanRewriteRule.LOG.isTraceEnabled )
                SPlanRewriteRule.LOG.trace("'to normal form' rewrites did not affect SNodePlan; skipping rest")
            return roots
        }
        if( SPlanRewriteRule.LOG.isTraceEnabled )
            SPlanRewriteRule.LOG.trace("Ran 'to normal form' rewrites $count times to yield: "+Explain.explainSPlan(roots))

        SNode.resetVisited(roots)
        for (node in roots)
            rRewriteSPlan(node, _rulesNormalForm)

        count = 0
        do {
            if( CHECK )
                SPlanValidator.validateSPlan(roots)
            var changed = false
            SNode.resetVisited(roots)
            for (node in roots)
                changed = rRewriteSPlan(node, _rulesToHopReady) || changed
            count++
        } while (changed)

        if( SPlanRewriteRule.LOG.isTraceEnabled )
            SPlanRewriteRule.LOG.trace("Ran 'to Hop-ready' rewrites $count times to yield: "+Explain.explainSPlan(roots))

        return roots
    }

    private fun rRewriteSPlan(node: SNode, rules: List<SPlanRewriteRule>): Boolean {
        if (node.visited)
            return false
        var changed = false

        //recursively process children
        for (i in node.inputs.indices) {
            var ci = node.inputs[i]

            //process children recursively first (to allow roll-up)

            //apply actual rewrite rules
            for (r in rules) {
                val result = r.rewriteNode(node, ci, i)
                when( result ) {
                    SPlanRewriteRule.RewriteResult.NoChange -> {}
                    is SPlanRewriteRule.RewriteResult.NewNode -> {
                        ci = result.newNode
                        changed = true
                    }
                }
            }

            //process children recursively after rewrites (to investigate pattern newly created by rewrites)
            changed = rRewriteSPlan(ci, rules) || changed
        }

        node.visited = true
        return changed
    }
}

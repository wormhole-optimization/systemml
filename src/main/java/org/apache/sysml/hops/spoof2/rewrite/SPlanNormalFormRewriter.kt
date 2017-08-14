package org.apache.sysml.hops.spoof2.rewrite

import java.util.ArrayList

import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.SPlanValidator
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriter.RewriterResult
import org.apache.sysml.utils.Explain

/**
 * 1. Apply the rewrite rules that get us into a normal form first, repeatedly until convergence.
 * 2. Apply RewriteNormalForm.
 * 3. Apply the rewrite rules that get us back to Hop-ready form, repeatedly until convergence.
 */
class SPlanNormalFormRewriter : SPlanRewriter {
    private val _rulesFirstOnce = listOf(
            RewriteDecompose()          // Subtract  + and *(-1);   ^2  Self-*
    )
    private val _rulesToNormalForm = listOf(
            RewriteBindElim(),
            RewriteSplitCSE(),          // split CSEs when they would block a sum-product rearrangement
            RewritePullAggAboveMult(),
            RewriteAggregateElim(),
            RewriteMultiplyPlusElim(),
            RewritePullPlusAboveMult()
    )
    private val _rulesNormalForm = listOf(
            RewritePushAggIntoPlus(),
            RewriteAggregateElim(),
            RewriteNormalForm()
    )
    private val _rulesToHopReady = listOf(
            RewriteMultiplyCSEToPower(), // RewriteNormalForm factorizes, so we can't get powers >2. Need to reposition. // Obsolete by RewriteElementwiseMultiplyChain?
            RewriteSplitMultiplyPlus(),
            RewritePushAggIntoMult()
            // todo RewriteRestoreCompound - subtract
    )

    companion object {
        /** Whether to invoke the SPlanValidator after every rewrite pass. */
        private const val CHECK = true

        val bottomUp = SPlanBottomUpRewriter()
        fun bottomUpRewrite(roots: ArrayList<SNode>): RewriterResult {
            val rr0 = bottomUp.rewriteSPlan(roots)
            if( rr0 is RewriterResult.NewRoots && rr0.newRoots !== roots ) {
                roots.clear()
                roots += rr0.newRoots
            }
            return rr0
        }
    }

    override fun rewriteSPlan(roots: ArrayList<SNode>): RewriterResult {
        var rr0 = bottomUpRewrite(roots)

        SNode.resetVisited(roots)
        for (root in roots)
            rRewriteSPlan(root, _rulesFirstOnce)

        var count = 0
        do {
            if( CHECK )
                SPlanValidator.validateSPlan(roots)
            var changed = false
            SNode.resetVisited(roots)
            for (root in roots)
                changed = rRewriteSPlan(root, _rulesToNormalForm) || changed
            count++
        } while (changed)

        if( count == 1 ) {
            if( SPlanRewriteRule.LOG.isTraceEnabled )
                SPlanRewriteRule.LOG.trace("'to normal form' rewrites did not affect SNodePlan; skipping rest")
            return rr0
        }
        if( SPlanRewriteRule.LOG.isTraceEnabled )
            SPlanRewriteRule.LOG.trace("Ran 'to normal form' rewrites $count times to yield: "+Explain.explainSPlan(roots))

        rr0 = bottomUpRewrite(roots)

        SNode.resetVisited(roots)
        for (node in roots)
            rRewriteSPlan(node, _rulesNormalForm)

        count = 0
        do {
            if( CHECK )
                SPlanValidator.validateSPlan(roots)
            var changed = false
            SNode.resetVisited(roots)
            for (root in roots)
                changed = rRewriteSPlan(root, _rulesToHopReady) || changed
            count++
        } while (changed)

        rr0 = bottomUpRewrite(roots)

        if( SPlanRewriteRule.LOG.isTraceEnabled )
            SPlanRewriteRule.LOG.trace("Ran 'to Hop-ready' rewrites $count times to yield: "+Explain.explainSPlan(roots))

        return RewriterResult.NewRoots(roots)
    }

    private fun rRewriteSPlan(node: SNode, rules: List<SPlanRewriteRule>): Boolean {
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
                    }
                }
            }

            //process children recursively after rewrites
            changed = rRewriteSPlan(child, rules) || changed
        }

        node.visited = true
        return changed
    }
}


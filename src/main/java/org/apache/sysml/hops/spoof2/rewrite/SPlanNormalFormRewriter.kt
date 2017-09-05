package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.spoof2.enu.NormalFormExploreEq
import org.apache.sysml.hops.spoof2.enu.RewriteNormalForm
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
    private val _ruleBindElim = listOf(
            RewriteBindElim(),
            RewriteMultiplyPlusSimplify()
    )
    private val _rulesToNormalForm: List<SPlanRewriteRule> = listOf(
//            RewriteBindElim(),
            RewriteSplitCSE(),          // split CSEs when they would block a sum-product rearrangement
            RewritePullAggAboveMult(),
            RewriteAggregateElim(),
            RewriteMultiplyPlusElim(),
            RewritePullPlusAboveMult()//,
            //RewritePullAggAbovePlus()
    )
    private val _rulesNormalFormPrior = listOf(
            RewritePushAggIntoPlus(),
            RewriteSplitCSE(),
            RewriteAggregateElim(),     // req. SplitCSE
            RewriteClearMxM(),
            RewritePushAggIntoPlus()    // req. ClearMxM
    )
    private val _normalFormRewrite: (ArrayList<SNode>) -> Unit =
//            { rewriteDown(it, listOf(RewriteNormalForm())) }
            { NormalFormExploreEq().rewriteSPlan(it) }
    private val _rulesToHopReady = listOf(
            RewriteMultiplyCSEToPower(), // RewriteNormalForm factorizes, so we can't get powers >2. Need to reposition. // Obsolete by RewriteElementwiseMultiplyChain?
            RewriteSplitMultiplyPlus(),
            RewritePushAggIntoMult(),
            RewriteClearMxM()
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
        rewriteDown(roots, _rulesFirstOnce)
        val rr0: RewriterResult = RewriterResult.NoChange //bottomUpRewrite(roots)

        // first bind elim
        var count0 = 0
        do {
            count0++
            if( CHECK ) SPlanValidator.validateSPlan(roots)
            val changed = rewriteDown(roots, _ruleBindElim)
        } while (changed)

        if( SPlanRewriteRule.LOG.isTraceEnabled )
            SPlanRewriteRule.LOG.trace("After bind elim: (count=$count0) "+Explain.explainSPlan(roots))

        var count = 0
        do {
            var changed: Boolean
            do {
                count++
                if (CHECK) SPlanValidator.validateSPlan(roots)
                changed = rewriteDown(roots, _rulesToNormalForm)
            } while( changed )
            changed = bottomUpRewrite(roots) is RewriterResult.NewRoots || changed
        } while (changed)

        if( count == 1 && count0 == 1 ) {
            if( SPlanRewriteRule.LOG.isTraceEnabled )
                SPlanRewriteRule.LOG.trace("'to normal form' rewrites did not affect SNodePlan; skipping rest")
            return rr0
        }
        if( SPlanRewriteRule.LOG.isTraceEnabled )
            SPlanRewriteRule.LOG.trace("Ran 'to normal form' rewrites $count times to yield: "+Explain.explainSPlan(roots))

        bottomUpRewrite(roots)
        if( CHECK ) SPlanValidator.validateSPlan(roots)

        rewriteDown(roots, _rulesNormalFormPrior)
        bottomUpRewrite(roots)
        _normalFormRewrite(roots)


        if( SPlanRewriteRule.LOG.isTraceEnabled )
            SPlanRewriteRule.LOG.trace("After processing normal form: "+Explain.explainSPlan(roots))

        count = 0
        do {
            count++
            if( CHECK ) SPlanValidator.validateSPlan(roots)
            var changed = rewriteDown(roots, _rulesToHopReady)
            changed = bottomUpRewrite(roots) is RewriterResult.NewRoots || changed
        } while (changed)

        if( CHECK ) SPlanValidator.validateSPlan(roots)
        if( SPlanRewriteRule.LOG.isTraceEnabled )
            SPlanRewriteRule.LOG.trace("Ran 'to Hop-ready' rewrites $count times to yield: "+Explain.explainSPlan(roots))

        return RewriterResult.NewRoots(roots)
    }

    private fun rewriteDown(roots: ArrayList<SNode>, rules: List<SPlanRewriteRule>): Boolean {
        SNode.resetVisited(roots)
        val changed = roots.fold(false) { changed, root -> rRewriteSPlan(root, rules) || changed }
        SNode.resetVisited(roots)
        return changed
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


package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.spoof2.enu.NormalFormExploreEq
import org.apache.sysml.hops.spoof2.enu.RewriteSplitBU_ExtendNormalForm

import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.SPlanValidator
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriter.RewriterResult
import org.apache.sysml.utils.Explain
import java.util.*

/**
 * 1. Apply the rewrite rules that get us into a normal form first, repeatedly until convergence.
 * 2. Apply RewriteNormalForm.
 * 3. Apply the rewrite rules that get us back to Hop-ready form, repeatedly until convergence.
 */
class SPlanNormalFormRewriter : SPlanRewriter {
    private val _rulesToNormalForm: List<SPlanRewriteRule> = listOf(
            RewriteMultiplyPlusSimplify(),
            RewriteSplitCSE(),          // split CSEs when they would block a sum-product rearrangement
            RewritePullAggAboveMult(),
            RewriteAggregateElim(),
            RewriteMultiplyPlusElim(),
            RewritePullPlusAboveMult(),
            RewritePushAggIntoPlus()
//            RewritePullAggAbovePlus()
    )
    private val _rulesNormalFormPrior = listOf<SPlanRewriteRule>(
            RewriteSplitBU_ExtendNormalForm()
//            RewritePushAggIntoPlus(),
//            RewriteSplitCSE(),
//            RewriteAggregateElim(),     // req. SplitCSE
//            RewriteClearMxM()
//            RewritePushAggIntoPlus(true)    // req. ClearMxM
    )
    private val _normalFormRewrite: (ArrayList<SNode>) -> Unit =
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
        val bottomUpNoElim = SPlanBottomUpRewriter(false)
        fun bottomUpRewrite(roots: ArrayList<SNode>, doElimCSE: Boolean = true): RewriterResult {
            val rr0 = if(doElimCSE) bottomUp.rewriteSPlan(roots) else bottomUpNoElim.rewriteSPlan(roots)
            if( rr0 is RewriterResult.NewRoots && rr0.newRoots !== roots ) {
                roots.clear()
                roots += rr0.newRoots
            }
            return rr0
        }
    }

    override fun rewriteSPlan(roots: ArrayList<SNode>): RewriterResult {
        var count = 0
        do {
            val startCount = count
            var changed: Boolean
            do {
                count++
                if (CHECK) SPlanValidator.validateSPlan(roots)
                changed = SPlanTopDownRewriter.rewriteDown(roots, _rulesToNormalForm)
            } while( changed )
            changed = bottomUpRewrite(roots) is RewriterResult.NewRoots || count > startCount+1
        } while (changed)

        if( count == 1 ) {
            if( SPlanRewriteRule.LOG.isTraceEnabled )
                SPlanRewriteRule.LOG.trace("'to normal form' rewrites did not affect SNodePlan; skipping rest")
            return RewriterResult.NoChange
        }
        if( SPlanRewriteRule.LOG.isTraceEnabled )
            SPlanRewriteRule.LOG.trace("Ran 'to normal form' rewrites $count times to yield: "+Explain.explainSPlan(roots))
        if( CHECK ) SPlanValidator.validateSPlan(roots)


        count = 0
        do {
            val startCount = count
            SPlanTopDownRewriter.rewriteDown(roots, _rulesNormalFormPrior)
            if( SPlanRewriteRule.LOG.isTraceEnabled )
                SPlanRewriteRule.LOG.trace("after before normal form: "+Explain.explainSPlan(roots))
            do {
                count++
                val changed = SPlanTopDownRewriter.rewriteDown(roots, _rulesToNormalForm)
            } while (changed)
            // dangerous! Do not put a bind-unbind in the middle of a block via BindUnify
            // avert this problem by doing a final RewriteSplitBU_ExtendNormalForm
            bottomUpRewrite(roots, false)
        } while( count != startCount+1 )
        SPlanTopDownRewriter.rewriteDown(roots, _rulesNormalFormPrior)
        if( SPlanRewriteRule.LOG.isTraceEnabled )
            SPlanRewriteRule.LOG.trace("Ran 'right before normal form' rewrites $count times")

        _normalFormRewrite(roots)

        if( SPlanRewriteRule.LOG.isTraceEnabled )
            SPlanRewriteRule.LOG.trace("After processing normal form: "+Explain.explainSPlan(roots))

        count = 0
        do {
            count++
            if( CHECK ) SPlanValidator.validateSPlan(roots)
            var changed = SPlanTopDownRewriter.rewriteDown(roots, _rulesToHopReady)
            changed = bottomUpRewrite(roots) is RewriterResult.NewRoots || changed
        } while (changed)

        if( CHECK ) SPlanValidator.validateSPlan(roots)
        if( SPlanRewriteRule.LOG.isTraceEnabled )
            SPlanRewriteRule.LOG.trace("Ran 'to Hop-ready' rewrites $count times to yield: "+Explain.explainSPlan(roots))

        return RewriterResult.NewRoots(roots)
    }
}

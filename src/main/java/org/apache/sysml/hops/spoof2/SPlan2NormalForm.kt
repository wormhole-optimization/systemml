package org.apache.sysml.hops.spoof2

import org.apache.sysml.hops.spoof2.enu.RewriteSplitBU_ExtendNormalForm
import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.SPlanValidator
import org.apache.sysml.hops.spoof2.rewrite.*
import org.apache.sysml.utils.Explain

/**
 * Put an SPlan DAG in normal form.
 */
@Deprecated("use the new InsertStyle version in place of this", ReplaceWith("SPlan2NormalForm_InsertStyle"))
object SPlan2NormalForm {
    private val _rulesToNormalForm: List<SPlanRewriteRule> = listOf(
//            RewriteMultiplyPlusSimplify(), // todo now a standalone rewriter
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

    /** Whether to invoke the SPlanValidator after every rewrite pass. */
    private const val CHECK = true

    private fun bottomUpRewrite(roots: ArrayList<SNode>, doElimCSE: Boolean = true): SPlanRewriter.RewriterResult {
        val rr0 = if(doElimCSE) SPlanBottomUpRewriter.rewriteSPlan(roots) else SPlanBottomUpRewriter.rewriteSPlan(roots, false)
        if( rr0 is SPlanRewriter.RewriterResult.NewRoots && rr0.newRoots !== roots ) {
            roots.clear()
            roots += rr0.newRoots
        }
        return rr0
    }

    fun rewriteSPlan(roots: ArrayList<SNode>): SPlanRewriter.RewriterResult {
        var count = 0
        do {
            val startCount = count
            var changed: Boolean
            do {
                count++
                if (CHECK) SPlanValidator.validateSPlan(roots)
                changed = SPlanTopDownRewriter.rewriteDown(roots, _rulesToNormalForm)
            } while( changed )
            changed = bottomUpRewrite(roots) is SPlanRewriter.RewriterResult.NewRoots || count > startCount+1
        } while (changed)

        if( count == 1 ) {
            if( SPlanRewriteRule.LOG.isTraceEnabled )
                SPlanRewriteRule.LOG.trace("'to normal form' rewrites did not affect SNodePlan; skipping rest")
            return SPlanRewriter.RewriterResult.NoChange
        }
        if( SPlanRewriteRule.LOG.isTraceEnabled )
            SPlanRewriteRule.LOG.trace("Ran 'to normal form' rewrites $count times to yield: "+ Explain.explainSPlan(roots))
        if(CHECK) SPlanValidator.validateSPlan(roots)


        count = 0
        do {
            val startCount = count
            SPlanTopDownRewriter.rewriteDown(roots, _rulesNormalFormPrior)
            if( SPlanRewriteRule.LOG.isTraceEnabled )
                SPlanRewriteRule.LOG.trace("after before normal form: "+ Explain.explainSPlan(roots))
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

        return SPlanRewriter.RewriterResult.NewRoots(roots)
    }


}
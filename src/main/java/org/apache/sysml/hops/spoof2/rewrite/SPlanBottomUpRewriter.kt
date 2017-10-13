package org.apache.sysml.hops.spoof2.rewrite

import org.apache.commons.logging.LogFactory
import org.apache.log4j.Level
import org.apache.log4j.Logger
import org.apache.sysml.conf.DMLConfig
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriter.RewriterResult
import org.apache.sysml.utils.Explain
import java.util.*

/**
 * Apply rewrites from the leaves up to the roots.
 */
class SPlanBottomUpRewriter(
        val doElimCSE: Boolean = true
) : SPlanRewriter {
    private val _rules: List<SPlanRewriteRuleBottomUp> = listOf(
            RewriteBindUnify()
    )

    companion object {
        /** Whether to invoke the SPlanValidator after every rewrite pass. */
        private const val CHECK = true
        private const val CHECK_DURING_RECUSION = false
        internal val LOG = LogFactory.getLog(SPlanBottomUpRewriter::class.java)!!

        //internal configuration flags
        private const val LDEBUG = DMLConfig.SPOOF_DEBUG
        init {
            if (LDEBUG) Logger.getLogger(SPlanBottomUpRewriter::class.java).level = Level.TRACE
        }

        fun getLeaves(roots: ArrayList<SNode>): MutableList<SNode> {
            SNode.resetVisited(roots)
            val dataops = LinkedList<SNode>()
            val literalops = LinkedList<SNodeData>()
            roots.forEach { _getLeaves(it, dataops, literalops) }
            SNode.resetVisited(roots)
            dataops += literalops
            return dataops
        }

        private fun _getLeaves(node: SNode, dataops: MutableList<SNode>, literalops: MutableList<SNodeData>) {
            if( node.visited )
                return
            if( node.inputs.isEmpty() ) {
                if( node is SNodeData && node.isLiteral )
                    literalops += node
                else
                    dataops += node
            } else
                node.inputs.forEach { _getLeaves(it, dataops, literalops) }
            node.visited = true
        }
    }

    override fun rewriteSPlan(roots: ArrayList<SNode>): RewriterResult {
        val cseElim = SPlanCSEElimRewriter(true, doElimCSE)
        val (rr0,leaves) = if(true) cseElim.rewriteSPlanAndGetLeaves(roots) else RewriterResult.NoChange to getLeaves(roots)
        var rr = rr0

        if( CHECK ) SPlanValidator.validateSPlan(roots)
//        if( LOG.isTraceEnabled )
//            LOG.trace("After CSE Elim:"+ Explain.explainSPlan(roots))

        var changed = false
        val collectedRoots = arrayListOf<SNode>()
        for( i in leaves.indices ) {
            val result = rRewriteSPlan(leaves[i], _rules, collectedRoots, roots)
            when( result ) {
                SPlanRewriteRule.RewriteResult.NoChange -> {}
                is SPlanRewriteRule.RewriteResult.NewNode -> {
                    leaves[i] = result.newNode
                    changed = true
                }
            }
        }
        SNode.resetVisited(roots)

        if(doElimCSE) {
            val cseElimNoLeaves = SPlanCSEElimRewriter(false, true)
            rr = rr.map(cseElimNoLeaves.rewriteSPlan(roots))
        }
        if( CHECK ) SPlanValidator.validateSPlan(roots)
//        if( LOG.isTraceEnabled )
//            LOG.trace("After bottom up rewrites:"+ Explain.explainSPlan(collectedRoots))

        // we rely on the order of roots during Hop reconstruction. Check that it hasn't changed.
        if( collectedRoots.toSet() != roots.toSet() )
            throw SNodeException("roots have changed as a result of bottom-up rewrites from $roots to $collectedRoots")

        return if( changed ) RewriterResult.NewRoots(roots) else rr
    }

    private fun rRewriteSPlan(node0: SNode, rules: List<SPlanRewriteRuleBottomUp>, collectedRoots: ArrayList<SNode>, allRoots: List<SNode>): SPlanRewriteRule.RewriteResult {
        var node = node0
        if (node.visited)
            return SPlanRewriteRule.RewriteResult.NoChange
        var changed: SPlanRewriteRule.RewriteResult = SPlanRewriteRule.RewriteResult.NoChange

        //apply actual rewrite rules
        for (r in rules) {
            val result = r.rewriteNodeUp(node)
            when( result ) {
                SPlanRewriteRule.RewriteResult.NoChange -> {}
                is SPlanRewriteRule.RewriteResult.NewNode -> {
                    node = result.newNode
                    changed = result
                    if( CHECK_DURING_RECUSION )
                        SPlanValidator.validateSPlan(allRoots, false)
                }
            }
        }

        if( node.parents.isEmpty() ) {
            collectedRoots += node
        } else {

            var i = 0
            while (i < node.parents.size) {
                val parent = node.parents[i]
                val result = rRewriteSPlan(parent, rules, collectedRoots, allRoots)
                if (changed == SPlanRewriteRule.RewriteResult.NoChange && result is SPlanRewriteRule.RewriteResult.NewNode)
                    changed = SPlanRewriteRule.RewriteResult.NewNode(node)
                i++
            }
        }
        node.visited = true
        return changed
    }
}

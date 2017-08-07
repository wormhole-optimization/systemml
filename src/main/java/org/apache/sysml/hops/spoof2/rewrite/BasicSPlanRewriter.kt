package org.apache.sysml.hops.spoof2.rewrite

import java.util.ArrayList

import org.apache.sysml.hops.spoof2.plan.SNode

/**
 * This program rewriter applies a variety of rule-based rewrites
 * on all hop dags of the given program in one pass over the entire
 * program.
 */
class BasicSPlanRewriter {
    private val _ruleSet: ArrayList<SPlanRewriteRule> = ArrayList()

    init {
        //initialize ruleSet (with fixed rewrite order)
        _ruleSet.add(RewriteBindElim())
        _ruleSet.add(RewritePullAggAboveMult())
        _ruleSet.add(RewriteAggregateElim())
        _ruleSet.add(RewriteMultiplyPlusElim()) // disrupts RewritePushAggIntoMult unless we choose a variable order and split the multiplies
        _ruleSet.add(RewriteSplitMultiplyPlus())
        _ruleSet.add(RewritePushAggIntoMult())
    }

    fun rewriteSPlan(roots: ArrayList<SNode>, rules: List<SPlanRewriteRule> = _ruleSet): ArrayList<SNode> {
        //one pass rewrite-descend (rewrite created pattern)
        SNode.resetVisited(roots)
        for (node in roots)
            rRewriteSPlan(node, rules, false)

//        SPlanRewriteRule.LOG.debug(Explain.explainSPlan(roots))

//        //one pass descend-rewrite (for rollup)
//        SNode.resetVisited(roots)
//        for (node in roots)
//            rRewriteSPlan(node, rules, false) // do not descendFirst because it messes up the visit flag
//        // the rewrite rules assume that the parents are visited first

        return roots
    }

    private fun rRewriteSPlan(node: SNode, rules: List<SPlanRewriteRule>, descendFirst: Boolean) {
        if (node.visited)
            return

        //recursively process children
        for (i in node.inputs.indices) {
            var ci = node.inputs[i]

            //process children recursively first (to allow roll-up)
            if (descendFirst)
                rRewriteSPlan(ci, rules, descendFirst)

            //apply actual rewrite rules
            for (r in rules) {
                val result = r.rewriteNode(node, ci, i)
                when( result ) {
                    SPlanRewriteRule.RewriteResult.NoChange -> {}
                    is SPlanRewriteRule.RewriteResult.NewNode -> {
                        ci = result.newNode
                    }
                }
            }

            //process children recursively after rewrites (to investigate pattern newly created by rewrites)
            if (!descendFirst)
                rRewriteSPlan(ci, rules, descendFirst)
        }

        node.visited = true
    }
}

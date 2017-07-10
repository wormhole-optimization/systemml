package org.apache.sysml.hops.spoof2.rewrite

import java.util.ArrayList

import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.utils.Explain

/**
 * This program rewriter applies a variety of rule-based rewrites
 * on all hop dags of the given program in one pass over the entire
 * program.
 */
class BasicSPlanRewriter {
    private val _ruleSet: ArrayList<SPlanRewriteRule> = ArrayList()

    init {
        //initialize ruleSet (with fixed rewrite order)
        _ruleSet.add(RewriteBindElimination())
        _ruleSet.add(RewritePullAggAboveMult()) // todo structure these in some loop that continues until there are no changes
        _ruleSet.add(RewriteAggregateElimination())
        _ruleSet.add(RewriteCombineMultiply()) // disrupts RewritePushAggIntoMult unless we choose a variable order and split the multiplies
        _ruleSet.add(RewriteSplitMultiply())
        _ruleSet.add(RewritePushAggIntoMult())
    }

    fun rewriteSPlan(roots: ArrayList<SNode>, rules: List<SPlanRewriteRule> = _ruleSet): ArrayList<SNode> {
        //one pass rewrite-descend (rewrite created pattern)
        SNode.resetVisited(roots)
        for (node in roots)
            rRewriteSPlan(node, rules, false)

        SPlanRewriteRule.LOG.debug(Explain.explainSPlan(roots))

        //one pass descend-rewrite (for rollup)
        SNode.resetVisited(roots)
        for (node in roots)
            rRewriteSPlan(node, rules, false) // do not descendFirst because it messes up the visit flag
        // the rewrite rules assume that the parents are visited first

        return roots
    }

    private fun rRewriteSPlan(node: SNode, rules: List<SPlanRewriteRule>, descendFirst: Boolean) {
        if (node.visited)
            return

        //recursively process children
        for (i in 0..node.inputs.size - 1) {
            var ci = node.inputs[i]

            //process children recursively first (to allow roll-up)
            if (descendFirst)
                rRewriteSPlan(ci, rules, descendFirst)

            //apply actual rewrite rules
            for (r in rules)
                ci = r.rewriteNode(node, ci, i)

            //process children recursively after rewrites (to investigate pattern newly created by rewrites)
            if (!descendFirst)
                rRewriteSPlan(ci, rules, descendFirst)
        }

        node.visited = true
    }
}

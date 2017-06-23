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
        _ruleSet.add(RewriteAggregateElimination())
        _ruleSet.add(RewriteDistributiveSumProduct())
        _ruleSet.add(RewriteTransposeElimination())
    }

    fun rewriteSPlan(roots: ArrayList<SNode>): ArrayList<SNode> {
        //one pass rewrite-descend (rewrite created pattern)
        SNode.resetVisited(roots)
        for (node in roots)
            rRewriteSPlan(node, false)

        //one pass descend-rewrite (for rollup)
        SNode.resetVisited(roots)
        for (node in roots)
            rRewriteSPlan(node, true)

        return roots
    }

    private fun rRewriteSPlan(node: SNode, descendFirst: Boolean) {
        if (node.visited)
            return

        //recursively process children
        for (i in 0..node.inputs.size - 1) {
            var ci = node.inputs[i]

            //process children recursively first (to allow roll-up)
            if (descendFirst)
                rRewriteSPlan(ci, descendFirst)

            //apply actual rewrite rules
            for (r in _ruleSet)
                ci = r.rewriteNode(node, ci, i)

            //process children recursively after rewrites (to investigate pattern newly created by rewrites)
            if (!descendFirst)
                rRewriteSPlan(ci, descendFirst)
        }

        node.visited = true
    }
}

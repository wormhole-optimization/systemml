package org.apache.sysml.hops.spoof2.enu2

import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.stripDead
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriteRule
import java.util.*


class RewriteSelectRandom: SPlanRewriteRule() {
    val rand = Random(2025L)
    override fun rewriteNode(parent: SNode, node: SNode, inputPosition: Int): RewriteResult {
        if (node is OrNode) {
            val nn = node.inputs[rand.nextInt(node.inputs.size)]
            node.inputs.forEach { inp ->
                inp.parents -= node
                if (inp !== nn) stripDead(inp)
            }
            node.parents.forEach { pa ->
                pa.inputs[pa.inputs.indexOf(node)] = nn
                nn.parents += pa
            }
            return RewriteResult.NewNode(nn)
        }
        return RewriteResult.NoChange
    }
}
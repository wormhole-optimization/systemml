package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.spoof2.enu2.OrNode
import org.apache.sysml.hops.spoof2.plan.SNode

class RewriteFlattenOrNode: SPlanRewriteRule() {
    override fun rewriteNode(parent: SNode, node: SNode, inputPosition: Int, allRoots: List<SNode>): RewriteResult {
        if (node is OrNode) {
            if (node.flatten())
                return RewriteResult.NewNode(node)
        }
        return RewriteResult.NoChange
    }
}
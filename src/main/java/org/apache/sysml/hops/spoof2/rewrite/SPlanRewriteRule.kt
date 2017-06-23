package org.apache.sysml.hops.spoof2.rewrite

import org.apache.commons.logging.LogFactory
import org.apache.sysml.hops.spoof2.plan.SNode

abstract class SPlanRewriteRule {

    abstract fun rewriteNode(parent: SNode, node: SNode, pos: Int): SNode

    companion object {
        internal val LOG = LogFactory.getLog(SPlanRewriteRule::class.java)!!
    }
}

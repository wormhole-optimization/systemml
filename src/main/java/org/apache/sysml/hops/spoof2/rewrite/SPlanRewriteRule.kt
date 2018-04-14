package org.apache.sysml.hops.spoof2.rewrite

import org.apache.commons.logging.LogFactory
import org.apache.log4j.Level
import org.apache.log4j.Logger
import org.apache.sysml.conf.DMLConfig
import org.apache.sysml.hops.spoof2.plan.SNode

abstract class SPlanRewriteRule {

    abstract fun rewriteNode(parent: SNode, node: SNode, inputPosition: Int, allRoots: List<SNode>): RewriteResult

    sealed class RewriteResult {
        data class NewNode(val newNode: SNode) : RewriteResult()
        object NoChange : RewriteResult() {
            override fun toString() = "NoChange"
        }
    }


    companion object {
        internal val LOG = LogFactory.getLog(SPlanRewriteRule::class.java)!!

        //internal configuration flags
        private const val LDEBUG = DMLConfig.SPOOF_DEBUG
        // for internal debugging only
        init {
            if (LDEBUG) Logger.getLogger(SPlanRewriteRule::class.java).level = Level.TRACE
        }
    }
}

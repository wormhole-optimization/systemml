package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.spoof2.plan.SNode
import java.util.ArrayList

interface SPlanRewriter {
    /** Rewrite an SNode DAG. Return whether the SNode DAG was modified or not. */
    fun rewriteSPlan(roots: ArrayList<SNode>): RewriterResult

    sealed class RewriterResult {
        data class NewRoots(val newRoots: ArrayList<SNode>) : RewriterResult() {
            override fun map(rr: RewriterResult) = rr as? NewRoots ?: this
            override fun toString() = "NewRoots($newRoots)"
        }

        object NoChange : RewriterResult() {
            override fun map(rr: RewriterResult) = rr
        }

        abstract fun map(rr: RewriterResult): RewriterResult
    }
}
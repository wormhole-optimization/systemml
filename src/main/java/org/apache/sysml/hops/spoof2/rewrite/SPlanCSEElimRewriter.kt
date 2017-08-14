package org.apache.sysml.hops.spoof2.rewrite

import org.apache.commons.logging.LogFactory
import org.apache.log4j.Level
import org.apache.log4j.Logger
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriter.RewriterResult
import java.util.ArrayList
import java.util.HashMap

/**
 * Eliminate Common Sub-Expressions.
 *
 * If mergeLeaves is true, SNodes with no input are merged according to type:
 * literal SNodeDatas are merged if they have the same data type and value;
 * SNodeData reads and SNodeExr are merged if they have the same hop id.
 *
 * Two parents of the same type and same children are merged into one, as follows:
 * ```
 *  X  Y  ->  X   Y
 *  |  |  ->   \ /
 *  f  f  ->    f
 * | \/ | ->   / \
 * | /\ | ->  A   B
 *  A  B  ->
 * ```
 *
 * Todo: extend to share equivalence.
 */
class SPlanCSEElimRewriter(
        val mergeLeaves: Boolean = true
) : SPlanRewriter {

    companion object {
        /** Whether to invoke the SPlanValidator after every rewrite pass. */
        private const val CHECK = true
        internal val LOG = LogFactory.getLog(SPlanCSEElimRewriter::class.java)!!

        //internal configuration flags
        private const val LDEBUG = true
        init {
            if (LDEBUG) Logger.getLogger(SPlanCSEElimRewriter::class.java).level = Level.TRACE
        }

        private fun SNode.getHopId() = when(this) {
            is SNodeData -> this.hop.hopID
            is SNodeExt -> this.hop.hopID
            else -> throw SNodeException(this, "does not have a hop id")
        }

        private fun replaceWithReal(node: SNode, real: SNode): Int {
            node.parents.forEach {
                it.inputs[it.inputs.indexOf(node)] = real
                real.parents += it
            }
            return node.parents.size
        }

        private fun SNodeData.getLiteralKey() = this.hop.valueType.toString()+'_'+this.hop.name
    }

    override fun rewriteSPlan(roots: ArrayList<SNode>): RewriterResult {
        return rewriteSPlanAndGetLeaves(roots).first
    }

    fun rewriteSPlanAndGetLeaves(roots: ArrayList<SNode>): Pair<RewriterResult, MutableList<SNode>> {
        val dataops = HashMap<Long, SNode>()
        val literalops = HashMap<String, SNode>() //key: <VALUETYPE>_<LITERAL>

        var changedLeaves = 0
        SNode.resetVisited(roots)
        if( mergeLeaves ) {
            for (root in roots)
                changedLeaves += rCSEElim_Leaves(root, dataops, literalops)
            SNode.resetVisited(roots)
        }
        var changed = 0
        for (root in roots)
            changed += rCSEElim(root)
        SNode.resetVisited(roots)
        if( CHECK )
            SPlanValidator.validateSPlan(roots)

        val rr = if( changed + changedLeaves > 0 ) {
            if( LOG.isTraceEnabled )
                LOG.trace("SPlanCSEElimRewriter: Eliminate $changedLeaves leaf and $changed internal node CSEs.")
            RewriterResult.NewRoots(roots)
        } else RewriterResult.NoChange
        return rr to (dataops.values + literalops.values).toMutableList()
    }

    private fun rCSEElim_Leaves(node: SNode,
                                dataops: HashMap<Long, SNode>,
                                literalops: HashMap<String, SNode>): Int {
        if( node.visited )
            return 0
        // do children first
        var changed = 0
        for (i in node.inputs.indices) {
            changed += rCSEElim_Leaves(node.inputs[i], dataops, literalops)
        }

        if( node.inputs.isEmpty() ) { // leaf
            val real = if( node is SNodeData && node.isLiteral ) {
                literalops.putIfAbsent(node.getLiteralKey(), node)
            } else {
                dataops.putIfAbsent(node.getHopId(), node)
            }
            if( real != null ) {
                changed += replaceWithReal(node, real)
            }
        }
        node.visited = true
        return changed
    }

    private fun rCSEElim(node: SNode): Int {
        if( node.visited )
            return 0
        // do children first
        var changed = 0
        for (i in node.inputs.indices) {
            changed += rCSEElim(node.inputs[i])
        }

        if( node.parents.size > 1 ) { // multiple consumers
            var i = 0
            while (i < node.parents.size-1) {
                var j = i+1
                while (j < node.parents.size) {
                    val h1 = node.parents[i]
                    val h2 = node.parents[j]
                    if( h1 !== h2 && h1.compare(h2) ) {
                        h2.parents.forEach {
                            it.inputs[it.inputs.indexOf(h2)] = h1
                            h1.parents += it
                        }
                        h2.inputs.forEach {
                            it.parents -= h2
                        }
                        changed++
                    } else
                        j++
                }
                i++
            }
        }
        node.visited = true
        return changed
    }
}

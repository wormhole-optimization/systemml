package org.apache.sysml.hops.spoof2.enu

import org.apache.commons.logging.LogFactory
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriteRule
import org.apache.sysml.utils.Statistics
import kotlin.coroutines.experimental.EmptyCoroutineContext.plus

/**
 * Fill an E-DAG.
 */
class NormalFormExploreEq : SPlanRewriteRule() {
    companion object {
        private val LOG = LogFactory.getLog(NormalFormExploreEq::class.java)!!
    }

    override fun rewriteNode(parent: SNode, node: SNode, pos: Int): RewriteResult {
        if( !SumProduct.isSumProductBlock(node))
            return RewriteResult.NoChange
        val spb = SumProduct.constructBlock(node, false)
        if( node.schema.names.any { !it.isBound() } )
            throw SNodeException(node, "Found unbound name in Sum-Product block; may not be handled incorrectly. $spb")
        if( LOG.isDebugEnabled )
            LOG.debug("Found Sum-Product Block:\n"+spb)

        // 0. Check if this normal form can be partitioned into two separate connected components.
        // This occurs if some portion of the multiplies produces a scalar.
        val CCnames = findConnectedNames(spb, spb.allSchema().names.first())
        if( CCnames != spb.allSchema().names.toSet() ) {
            val NCnames = spb.allSchema().names - CCnames

            val CCspb = SumProduct.Block(
                    spb.sumBlocks.map { SumBlock(it.op, it.names.filter { it in CCnames }) }
                            .filter { it.names.isNotEmpty() },
                    spb.product,
                    spb.edges.filter { it.schema.names.any { it in CCnames } }
                            .map { it.deepCopy() }
            )
            val NCspb = SumProduct.Block(
                    spb.sumBlocks.map { SumBlock(it.op, it.names.filter { it in NCnames }) }
                            .filter { it.names.isNotEmpty() },
                    spb.product,
                    spb.edges.filter { it.schema.names.any { it in NCnames } }
                            .map { it.deepCopy() }
            )
            spb.sumBlocks.clear()
            spb.edges.clear()
            spb.edges += CCspb
            spb.edges += NCspb

            if( LOG.isDebugEnabled )
                LOG.debug("Partition Sum-Product block into disjoint components:\n" +
                        "Component 1: $CCspb\n" +
                        "Component 2: $NCspb")

            return RewriteResult.NewNode(spb.applyToNormalForm(node)) // these will be handled as disjoint sub-problems in SPlanNormalFormRewriter at next recursion
        }

        // Create ENode
        val parents = ArrayList(node.parents)
        val eNode = ENode(node)
        eNode.parents.addAll(parents)
        parents.forEach { it.inputs[it.inputs.indexOf(node)] = eNode }
        // disconnect and dead code elim the input
        node.parents.clear() // can no longer use applyToNormalForm
        eNode.inputs.clear()
//        stripDead(node, spb.getAllInputs()) // performed by constructBlock()

        val numFactorCalls = factorAndInsert(eNode, spb)
        if( LOG.isTraceEnabled )
            LOG.trace("numFactorCalls: $numFactorCalls")

        return RewriteResult.NewNode(eNode)
    }

    private fun factorAndInsert(eNode: ENode, spb: SumProduct.Block): Int {
        if (spb.edgesGroupByIncidentNames().size == 1) {
            // all edges fit in a single group; nothing to do
            insert(eNode, spb)
            return 1
        }

        // 1. Multiply within groups
        spb.edgesGroupByIncidentNames().forEach { (_, edges) ->
            if (edges.size > 1) {
                // Create a Block on just these inputs.
                // Move these inputs to the new block and wire the new block to this block.
                // Push aggregations down if they are not join conditions (present in >1 edge).
                spb.factorEdgesToBlock(edges)
                if (LOG.isTraceEnabled)
                    LOG.trace("Isolating edge group\n[${edges.joinToString(",\n")}]")
            }
        }

        // Done if no aggregations remain
        if (spb.aggNames().isEmpty()) {
            insert(eNode, spb)
            return 1
        }

        // Determine what variables we could eliminate at this point
        val eligibleAggNames = spb.eligibleAggNames()
        // Prune down to the agg names with minimum degree
        val tmp = eligibleAggNames.map { it to (spb.nameToAdjacentNames()[it]!! - it).size }
        val minDegree = tmp.map { it.second }.min()!!
        check(minDegree <= 2) { "Minimum degree is >2. Will form tensor intermediary. In spb $spb" }
        val minDegreeAggNames = tmp.filter { it.second == minDegree }.map { it.first }

        // fork on the different possible agg names
        return minDegreeAggNames.sumBy { elimName ->
            val incidentEdges = spb.nameToIncidentEdge()[elimName]!!
            if( incidentEdges.size == spb.edges.size && spb.aggNames().isEmpty() ) { // if all edges remaining touch this one, nothing to do.
                insert(eNode, spb)
                return 1
            }

            val factoredSpb = spb.deepCopy()
            factoredSpb.factorEdgesToBlock(incidentEdges)
            factorAndInsert(eNode, factoredSpb)
        }
    }

    private fun insert(eNode: ENode, spb: SumProduct.Block) {

    }


//    private fun trackStatistics(spb: SumProduct.Block) {
//        // Tracks largest sum-product statistics; see RewriteNormalForm, Statistics, AutomatedTestBase
//        val recSchema = spb.recUnionSchema()
//
//        val thisSize = numForks // spb.edges.size + recSchema.size +
//        var oldLargestSize: Int
//        do {
//            oldLargestSize = Statistics.spoof2NormalFormNameLength.get()
//        } while(thisSize > oldLargestSize && !Statistics.spoof2NormalFormNameLength.compareAndSet(oldLargestSize, thisSize))
//        // not exactly thread safe because we need to lock the other fields, but good enough for this hack.
//
//        if( thisSize > oldLargestSize ) {
//            Statistics.spoof2NormalFormAggs = recSchema.toString()
//            Statistics.spoof2NormalFormFactoredSpb = spb.toString() //.edges.map { it.schema }.toString()
//            Statistics.spoof2NormalFormNumForks = numForks
//            Statistics.spoof2NormalFormChanged.set(true)
//        }
//    }


    private fun findConnectedNames(spb: SumProduct.Block, name: Name): Set<Name> {
        return mutableSetOf<Name>().also { rFindConnectedNames(spb.nameToAdjacentNames(), name, it) }
    }

    /** Depth first search to find connected names. */
    private fun rFindConnectedNames(adjMap: Map<Name, Set<Name>>, name: Name, foundNames: MutableSet<Name>) {
        val adjacent = adjMap[name] ?: return
        val adjacentNotFound = adjacent - foundNames
        foundNames += adjacentNotFound
        adjacentNotFound.forEach { rFindConnectedNames(adjMap, it, foundNames) }
    }

}
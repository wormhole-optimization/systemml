package org.apache.sysml.hops.spoof2.rewrite

import org.apache.commons.logging.LogFactory
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.utils.Statistics

/**
 * Applies to `sum(+)-mult(*)` when mult has no foreign parents and has >2 inputs.
 */
class RewriteNormalForm : SPlanRewriteRule() {
    companion object {
        private val LOG = LogFactory.getLog(RewriteNormalForm::class.java)!!
    }

    override fun rewriteNode(parent: SNode, node: SNode, pos: Int): RewriteResult {
        if( !SumProduct.isSumProductBlock(node))
            return RewriteResult.NoChange
        val spb = SumProduct.constructBlock(node)
        if( node.schema.names.any { !it.isBound() } ) {
            LOG.warn("Found unbound name in Sum-Product block; may not be handled incorrectly. $spb")
        }

        if( LOG.isDebugEnabled )
            LOG.debug("Found Sum-Product Block:\n"+spb)


//        val agg = node as SNodeAggregate
//        val mult = agg.inputs[0] as SNodeNary
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


//            // partition the names by CCnames
//            // create:  CC-edges <<- aggp[CC-aggs] <- new-mult -> agg[not-CC-aggs] ->> not-CC-edges
//            val (CCedges, NCedges) = mult.inputs.partition { it.schema.names.first() in CCnames }
//            mult.inputs.forEach { it.parents.removeAt(it.parents.indexOf(mult)) }
//            val CCaggNames = agg.aggreateNames.intersect(CCnames)
//            val NCaggNames = agg.aggreateNames - CCaggNames
//
//            // For CC and NC, don't create mult if only one input; don't create agg if no aggregation.
//            val CCmult = if (CCedges.size == 1) CCedges.first() else SNodeNary(mult.op, CCedges)
//            val CCagg = if (CCaggNames.isEmpty()) CCmult else SNodeAggregate(agg.op, CCmult, CCaggNames)
//            val NCmult = if (NCedges.size == 1) NCedges.first() else SNodeNary(mult.op, NCedges)
//            val NCagg = if (NCaggNames.isEmpty()) NCmult else SNodeAggregate(agg.op, NCmult, NCaggNames)
//            val newMult = SNodeNary(mult.op, CCagg, NCagg)
//
//            val parents = ArrayList(agg.parents)
//            for( p in parents )
//                SNodeRewriteUtils.replaceChildReference(p, agg, newMult)
//            for( p in agg.parents )
//                p.refreshSchemasUpward() // playing it safe, not sure if this is necessary

            if( LOG.isDebugEnabled )
                LOG.debug("Partition Sum-Product block into disjoint components:\n" +
                        "Component 1: $CCspb\n" +
                        "Component 2: $NCspb")

            return RewriteResult.NewNode(spb.applyToNormalForm(node)) // these will be handled as disjoint sub-problems in SPlanNormalFormRewriter at next recursion
        }

        numForks = 0

        var (spbNew, spbCost) = factorSumProduct(spb)

        if( spbNew.sumBlocks.isEmpty() && spbNew.edges.size == 1 && spbNew.edges[0] is SumProduct.Block )
            spbNew = spbNew.edges[0] as SumProduct.Block

        if( LOG.isDebugEnabled )
            LOG.debug("New SumProduct.Block found with cost $spbCost (numForks=$numForks)\n" +
                    "$spbNew")

        trackStatistics(spb)

        return RewriteResult.NewNode(spbNew.applyToNormalForm(node))
    }

    var numForks = 0

    private fun factorSumProduct(spb: SumProduct.Block): Pair<SumProduct.Block, SPCost> {
        if (spb.edgesGroupByIncidentNames().size == 1) {
            // all edges fit in a single group; nothing to do
            return spb to SPCost.costFactoredBlock(spb)
        }

        // 1. Multiply within groups
        spb.edgesGroupByIncidentNames().forEach { (_, edges) ->
            if (edges.size > 1) {
                // Create a Block on just these inputs.
                // Move these inputs to the new block and wire the new block to this block.
                // Push aggregations down if they are not join conditions (present in >1 edge).
                spb.factorEdgesToBlock(edges)
                if (LOG.isDebugEnabled)
                    LOG.debug("Isolating edge group $edges")
            }
        }

        // Done if no aggregations remain
        if (spb.aggNames().isEmpty())
            return spb to SPCost.costFactoredBlock(spb)

        // Determine what variables we could eliminate at this point
        val eligibleAggNames = spb.eligibleAggNames()
        // Prune down to the agg names with minimum degree
        val tmp = eligibleAggNames.map { it to (spb.nameToAdjacentNames()[it]!! - it).size }
        val minDegree = tmp.map { it.second }.min()!!
        check(minDegree <= 2) { "Minimum degree is >2. Will form tensor intermediary. In spb $spb" }
        val minDegreeAggNames = tmp.filter { it.second == minDegree }.map { it.first }
        numForks += minDegreeAggNames.size

        // fork on the different possible agg names
        val (bestSpb, bestCost) = minDegreeAggNames.map { elimName ->
            val incidentEdges = spb.nameToIncidentEdge()[elimName]!!
            if( incidentEdges.size == spb.edges.size && spb.aggNames().isEmpty() ) // if all edges remaining touch this one, nothing to do.
                return spb to SPCost.costFactoredBlock(spb)

            val factoredSpb = spb.deepCopy()
            factoredSpb.factorEdgesToBlock(incidentEdges)
            val (newSpb, cost) = factorSumProduct(factoredSpb)
            newSpb to cost
        }.minBy { it.second }!!

        return bestSpb to bestCost
    }

//    private fun elimName(spb: SumProduct.Block, elimName: Name): SumProduct.Block {
//        val incidentEdges = spb.nameToIncidentEdge()[elimName]!!
//        if( incidentEdges.size == spb.edges.size ) // if all edges remaining touch this one, nothing to do.
//            return spb
//        spb.factorEdgesToBlock(incidentEdges)
//        return spb
//    }

//    private fun temp(spbInitial: SumProduct.Block) {
//        var spb = spbInitial
//        val mult = agg.inputs[0] as SNodeNary
//
//        // 1. Multiply within groups
//        if( spb.edgesGroupByIncidentNames.size == 1 ) {
//            // all edges fit in a single group; chain them
//            RewriteMultiplySplit.splitMultiply(mult)
//            assert(mult.inputs.size == 2)
//            return agg
//        }
//        spb.edgesGroupByIncidentNames.forEach { (_, edges) ->
//            if( edges.size > 1 ) {
//                val edgeIds = edges.map { it as SumProduct.Input; it.id }
//                val edgeNodes = mult.inputs.filter { it.id in edgeIds }
//
//                // Create a multiply just with these edgeNodes, then split it.
//                mult.inputs.removeIf { it.id in edgeIds }
//                edgeNodes.forEach { it.parents.remove(mult) }
//                val newMult = SNodeNary(mult.op, edgeNodes)
//                mult.inputs += newMult
//                newMult.parents += mult
//                RewriteMultiplySplit.splitMultiply(newMult)
//                mult.refreshSchemasUpward()
//
//                if (LOG.isDebugEnabled)
//                    LOG.debug("Isolating edge group $edgeNodes under new $newMult id=${newMult.id} ${newMult.schema}")
//            }
//        }
//        // If we go down to 2 inputs, we are done.
//        if( !SumProduct.isSumProductBlock(agg) )
//            return agg
//
//        return agg
//    }

    private fun trackStatistics(spb: SumProduct.Block) {
        // Tracks largest sum-product statistics; see RewriteNormalForm, Statistics, AutomatedTestBase
        val recSchema = spb.recUnionSchema()

        val thisSize = numForks // spb.edges.size + recSchema.size +
        var oldLargestSize: Int
        do {
            oldLargestSize = Statistics.spoof2NormalFormNameLength.get()
        } while(thisSize > oldLargestSize && !Statistics.spoof2NormalFormNameLength.compareAndSet(oldLargestSize, thisSize))
        // not exactly thread safe because we need to lock the other fields, but good enough for this hack.

        if( thisSize > oldLargestSize ) {
            Statistics.spoof2NormalFormAggs = recSchema.toString()
            Statistics.spoof2NormalFormFactoredSpb = spb.toString() //.edges.map { it.schema }.toString()
            Statistics.spoof2NormalFormNumForks = numForks
            Statistics.spoof2NormalFormChanged.set(true)
        }
    }


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





//    private fun costQuery(spb: SumProductBlock, elimName: Name): Pair<SPCost, List<Name>> {
//        // 1. Form elim neighbor groups
//        TODO()
//    }



}

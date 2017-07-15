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
        val agg = node as SNodeAggregate
        val mult = agg.inputs[0] as SNodeNary
        if( mult.schema.names.any { !it.isBound() } ) {
            LOG.warn("Found unbound name in Sum-Product block; may not be handled incorrectly. $spb")
        }

        if( LOG.isDebugEnabled )
            LOG.debug(spb)

        trackStatistics(spb)

        // 0. Check if this normal form can be partitioned into two separate connected components.
        // This occurs if some portion of the multiplies produces a scalar.
        val CCnames = findConnectedNames(spb, spb.names.first())
        if( CCnames != spb.names ) {
            val NCnames = spb.names - CCnames
            // partition the names by CCnames
            // create:  CC-edges <<- aggp[CC-aggs] <- new-mult -> agg[not-CC-aggs] ->> not-CC-edges
            val (CCedges, NCedges) = mult.inputs.partition { it.schema.names.first() in CCnames }
            mult.inputs.forEach { it.parents.removeAt(it.parents.indexOf(mult)) }
            val CCaggNames = agg.aggreateNames.intersect(CCnames)
            val NCaggNames = agg.aggreateNames - CCaggNames

            // For CC and NC, don't create mult if only one input; don't create agg if no aggregation.
            val CCmult = if (CCedges.size == 1) CCedges.first() else SNodeNary(mult.op, CCedges)
            val CCagg = if (CCaggNames.isEmpty()) CCmult else SNodeAggregate(agg.op, CCmult, CCaggNames)
            val NCmult = if (NCedges.size == 1) NCedges.first() else SNodeNary(mult.op, NCedges)
            val NCagg = if (NCaggNames.isEmpty()) NCmult else SNodeAggregate(agg.op, NCmult, NCaggNames)
            val newMult = SNodeNary(mult.op, CCagg, NCagg)

            val parents = ArrayList(agg.parents)
            for( p in parents )
                SNodeRewriteUtils.replaceChildReference(p, agg, newMult)
            for( p in agg.parents )
                p.refreshSchemasUpward() // playing it safe, not sure if this is necessary

            if( LOG.isDebugEnabled )
                LOG.debug("Detected Sum-Product block that can be partitioned into disjoint connected components:\n" +
                        "\tComponent 1: ${CCedges.size} edge with names $CCnames ${if(CCagg is SNodeAggregate) "aggregating" else "no agg"} at $CCagg id=${CCagg.id}\n" +
                        "\tComponent 2: ${NCedges.size} edge with names $NCnames ${if(NCagg is SNodeAggregate) "aggregating" else "no agg"} at $NCagg id=${NCagg.id}")

            return RewriteResult.NewNode(newMult) // these will be handled as disjoint sub-problems in SPlanNormalFormRewriter at next recursion
        }


        return RewriteResult.NewNode(solveSumProduct(agg, spb))


//        // 1. Brute force variable order. spb.aggNames.size! choices.
//        // Cost each variable order.
//        var bestCost = SPCost.MAX_COST
//        var bestOrder = listOf<Name>()
//        for (elimName in spb.aggNames) {
//            val (cost, order) = costQuery(spb, elimName)
//            // Does not consider the cost of multiplying vectors over non-aggregated names,
//            // but the cost of multiplying those is the same for all elimination orders, so it is okay not to add it here.
//            if( cost < bestCost ) {
//                bestCost = cost
//                bestOrder = order + elimName
//            }
//        }
//        bestOrder = bestOrder.reversed()
//        if( LOG.isDebugEnabled )
//            LOG.debug("Best order at cost $bestCost: $bestOrder")

        // 2. Re-order the multiplies into the new order.
        // todo


//        return RewriteResult.NoChange
    }
    private fun solveSumProduct(agg: SNodeAggregate, spbInitial: SumProduct.Block): SNodeAggregate {
        var spb = spbInitial
        val mult = agg.inputs[0] as SNodeNary

        // 1. Multiply within groups
        if( spb.edgesGroupByIncidentNames.size == 1 ) {
            // all edges fit in a single group; chain them
            RewriteSplitMultiply.splitMultiply(mult)
            assert(mult.inputs.size == 2)
            return agg
        }
        spb.edgesGroupByIncidentNames.forEach { (_, edges) ->
            if( edges.size > 1 ) {
                val edgeIds = edges.map { it as SumProduct.Edge; it.id }
                val edgeNodes = mult.inputs.filter { it.id in edgeIds }

                // Create a multiply just with these edgeNodes, then split it.
                mult.inputs.removeIf { it.id in edgeIds }
                edgeNodes.forEach { it.parents.remove(mult) }
                val newMult = SNodeNary(mult.op, edgeNodes)
                mult.inputs += newMult
                newMult.parents += mult
                RewriteSplitMultiply.splitMultiply(newMult)
                mult.refreshSchemasUpward()

                if (LOG.isDebugEnabled)
                    LOG.debug("Isolating edge group $edgeNodes under new $newMult id=${newMult.id} ${newMult.schema}")
            }
        }
        // If we go down to 2 inputs, we are done.
        if( !SumProduct.isSumProductBlock(agg) )
            return agg

        return agg
//        // 2. Eliminate aggregated names, in order of the lowest degree one.
//        while( spb.aggNames.isNotEmpty() ) {
//            val (elimName,elimAdjNames) = spb.nameToAdjacentNames.minBy { (name,adjNames) ->
//                (adjNames - name).size
//            }!!
//            when( elimAdjNames.size ) {
//                0 -> {}
//                1 -> {
//
//                }
//            }
//        }
    }

    private fun trackStatistics(spb: SumProduct.Block) {
        // Tracks largest sum-product statistics; see RewriteNormalForm, Statistics, AutomatedTestBase
        val thisSize = spb.inputs.size
        var oldLargestSize: Int
        do {
            oldLargestSize = Statistics.spoof2NormalFormNameLength.get()
        } while(thisSize > oldLargestSize && !Statistics.spoof2NormalFormNameLength.compareAndSet(oldLargestSize, thisSize))
        // not exactly thread safe because we need to lock the other fields, but good enough for this hack.

        if( thisSize > oldLargestSize ) {
            Statistics.spoof2NormalFormAggs = spb.aggNames.toString()
            Statistics.spoof2NormalFormInputSchemas = spb.inputs.map { it.schema }.toString()
            Statistics.spoof2NormalFormChanged.set(true)
        }
    }


    private fun findConnectedNames(spb: SumProduct.Block, name: Name): Set<Name> {
        return mutableSetOf<Name>().also { rFindConnectedNames(spb, name, it) }
    }

    /** Depth first search to find connected names. */
    private fun rFindConnectedNames(spb: SumProduct.Block, name: Name, foundNames: MutableSet<Name>) {
        val adjacent = spb.nameToAdjacentNames[name] ?: return
        val adjacentNotFound = adjacent - foundNames
        foundNames += adjacentNotFound
        adjacentNotFound.forEach { rFindConnectedNames(spb, it, foundNames) }
    }




    data class SPCost(
            val nMultiply: Long = 0L,
            val nAdd: Long = 0L,
            val nMemory: Long = 0L
    ) : Comparable<SPCost> {

        companion object {
            val MAX_COST = SPCost(Long.MAX_VALUE, Long.MAX_VALUE, Long.MAX_VALUE)
        }
        override fun compareTo(other: SPCost): Int {
            // todo consider memory - check if below distributed threshold
            return (nMultiply + nAdd - other.nMultiply - other.nAdd).toInt()
        }

    }

//    private fun costQuery(spb: SumProductBlock, elimName: Name): Pair<SPCost, List<Name>> {
//        // 1. Form elim neighbor groups
//        TODO()
//    }



}

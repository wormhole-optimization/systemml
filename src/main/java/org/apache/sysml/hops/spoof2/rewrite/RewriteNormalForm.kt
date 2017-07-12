package org.apache.sysml.hops.spoof2.rewrite

import org.apache.commons.logging.LogFactory
import org.apache.sysml.hops.Hop
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
        val spb = isSumProductBlock(node) ?: return RewriteResult.NoChange
        val agg = node as SNodeAggregate
        val mult = agg.inputs[0] as SNodeNary
        if( mult.schema.names.any { !it.isBound() } ) {
            LOG.warn("Found unbound name in Sum-Product block; may not be handled incorrectly. $spb")
        }

        if( LOG.isDebugEnabled )
            LOG.debug(spb)

        // Tracks largest sum-product statistics; see RewriteNormalForm, Statistics, AutomatedTestBase
        val thisSize = spb.edges.size
        var oldLargestSize: Int
        do {
            oldLargestSize = Statistics.spoof2NormalFormNameLength.get()
        } while(thisSize > oldLargestSize && !Statistics.spoof2NormalFormNameLength.compareAndSet(oldLargestSize, thisSize))
        // not exactly thread safe because we need to lock the other fields, but good enough for this hack.

        if( thisSize > oldLargestSize ) {
            Statistics.spoof2NormalFormAggs = spb.aggNames.toString()
            Statistics.spoof2NormalFormInputSchemas = spb.edges.toString()
            Statistics.spoof2NormalFormChanged.set(true)
        }

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

        return RewriteResult.NoChange
    }

    private fun findConnectedNames(spb: SumProductBlock, name: Name): Set<Name> {
        return mutableSetOf<Name>().also { rFindConnectedNames(spb, name, it) }
    }

    /** Depth first search to find connected names. */
    private fun rFindConnectedNames(spb: SumProductBlock, name: Name, foundNames: MutableSet<Name>) {
        val adjacent = spb.nameToAdjacentNames[name] ?: return
        val adjacentNotFound = adjacent - foundNames
        foundNames += adjacentNotFound
        adjacentNotFound.forEach { rFindConnectedNames(spb, it, foundNames) }
    }

    private fun isSumProductBlock(agg: SNode): SumProductBlock? {
        if( agg is SNodeAggregate && agg.op == Hop.AggOp.SUM ) {
            val mult = agg.inputs[0]
            if( mult is SNodeNary && mult.op == SNodeNary.NaryOp.MULT
                    && mult.parents.size == 1 && mult.inputs.size > 2 ) {
                return SumProductBlock(agg)
            }
        }
        return null
    }

    private data class Edge(
            val id: Long,
            val schema: Schema,
            val nnz: Long?
    ) {
        constructor(snode: SNode)
                : this(snode.id, Schema(snode.schema), null) // todo fill with nnz estimate
    }

    private data class SumProductBlock(
            val edges: List<Edge>,
            val aggNames: Set<Name>,
            val aggOp: Hop.AggOp,
            val multOp: SNodeNary.NaryOp,
            val aggId: Long
    ) {
        constructor(aggNode: SNodeAggregate) : this(
                aggNode.inputs[0].inputs.map(::Edge),
                HashSet(aggNode.aggreateNames),
                aggNode.op, (aggNode.inputs[0] as SNodeNary).op, aggNode.id
        )
        /** Map of name to all edges touching that name. */
        val nameToIncidentEdge: Map<Name,List<Edge>> = edges.flatMap { edge ->
            edge.schema.names.map { name -> name to edge }
        }.groupBy(Pair<Name,Edge>::first).mapValues { (_,v) -> v.map(Pair<Name,Edge>::second) }

        val names = nameToIncidentEdge.keys

        /** Map of name to all names adjacent to it via some edge. */
        val nameToAdjacentNames: Map<Name,Set<Name>> = nameToIncidentEdge.mapValues { (_,edges) ->
            edges.flatMap { it.schema.names }.toSet()
        }

        override fun toString(): String {
            return "SumProductBlock (+=$aggOp) (*=$multOp) (aggId=$aggId)\n" +
                    "\tnames: $names aggregating $aggNames\n" +
                    "\tedges: ${edges.map { it.schema.names }}"
        }
    }

//    private data class MultiplyBlock(
//            val multOp: SNodeNary.NaryOp,
//            val names: List<Name>,
//            val inputs: List<Schema>
//    )
}
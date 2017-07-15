package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.spoof2.plan.*

data class SumBlock(
        val sum: Hop.AggOp,
        val names: Set<Name>
)

/**
 * Treat this class as immutable (even though it is technically possible to modify the schema and various lists.
 * A SumProduct is either an Edge (base case, representing an SNode input) or a Block (inductive case, representing
 * some number of sums over the product of SumProducts).
 */
sealed class SumProduct {

    abstract val schema: Schema
    abstract val nnz: Long?

    companion object {

        val ALLOWED_SUMS = setOf(Hop.AggOp.SUM)
        val ALLOWED_PRODUCTS = setOf(SNodeNary.NaryOp.MULT)

        fun isSumProductBlock(_top: SNode): Boolean {
            var top = _top
            while (top is SNodeAggregate) {
                if( top.op !in ALLOWED_SUMS )
                    return false
                // no foreign parents below the top agg
                if( top !== _top && top.parents.size > 1 )
                    return false
                top = top.inputs[0]
            }
            if( top !is SNodeNary || top.op !in ALLOWED_PRODUCTS || top.parents.size > 1 || top.inputs.size <= 2)
                return false
            return true
        }

        fun constructBlock(_top: SNode): Block {
            var top = _top
            val sumBlocks = ArrayList<SumBlock>()
            while (top is SNodeAggregate) {
                sumBlocks += SumBlock(top.op, top.aggreateNames.toSet())
                top = top.inputs[0]
            }
            require( top is SNodeNary ) {"sum-product block does not have a product; found $top id=${top.id}"}
            top as SNodeNary
            val product = top.op
            val edges = top.inputs.map(::Edge)
            return Block(sumBlocks, product, edges)
        }
    }

    data class Edge(
            val id: Long,
            override val schema: Schema,
            override val nnz: Long?
    ) : SumProduct() {
        constructor(snode: SNode)
                : this(snode.id, Schema(snode.schema), null) // todo fill with nnz estimate

        // Edges are equal if they have the same id.
        override fun equals(other: Any?): Boolean {
             if (this === other) return true
             if (other?.javaClass != javaClass) return false
             other as Edge
             return id == other.id
         }
        override fun hashCode() = id.hashCode()

     }

    data class Block(
            val sumBlocks: List<SumBlock>,
            val product: SNodeNary.NaryOp,
            val inputs: List<SumProduct>
    ) : SumProduct() {
        override val schema = inputs.fold(Schema()) { schema, sp -> schema.apply{unionWithBound(sp.schema)} }
        override val nnz: Long? = null // todo compute nnz estimate

        val aggNames = sumBlocks.map(SumBlock::names).reduce { a,b -> a+b}

        /** Map of name to all edges touching that name. */
        val nameToIncidentEdge: Map<Name,List<SumProduct>> = inputs.flatMap { edge ->
            edge.schema.names.map { name -> name to edge }
        }.groupBy(Pair<Name,SumProduct>::first).mapValues { (_,v) -> v.map(Pair<Name,SumProduct>::second) }

        val names = nameToIncidentEdge.keys

        /** Map of name to all names adjacent to it via some edge. */
        val nameToAdjacentNames: Map<Name,Set<Name>> = nameToIncidentEdge.mapValues { (_,edges) ->
            edges.flatMap { it.schema.names }.toSet()
        }

        val edgesGroupByIncidentNames: Map<Set<Name>, List<SumProduct>> = inputs.groupBy { it.schema.names.toSet() }
    }



}














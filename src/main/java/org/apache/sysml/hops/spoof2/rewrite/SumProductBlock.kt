package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.spoof2.plan.*


private const val SHOW_NNZ = false


class SumBlock private constructor(
        val op: Hop.AggOp,
        val names: MutableSet<Name>
) {
    constructor(sum: Hop.AggOp, names: Collection<Name>)
            : this(sum, HashSet(names))
    constructor(sum: Hop.AggOp, vararg names: Name)
            : this(sum, HashSet(names.asList()))
    fun deepCopy() = SumBlock(op, HashSet(names))
    override fun toString(): String {
        return "$op$names"
    }

}

/**
 * Treat this class as immutable (even though it is technically possible to modify the schema and various lists.
 * A SumProduct is either an Input (base case, representing an SNode input) or a Block (inductive case, representing
 * some number of sums over the product of SumProducts).
 */
sealed class SumProduct {

    /** Schema of non-aggregated attributes. The schema emitting from this SumProduct. */
    abstract val schema: Schema
    abstract val nnz: Long?
    abstract fun deepCopy(): SumProduct

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
                sumBlocks += SumBlock(top.op, top.aggreateNames.toMutableSet())
                top = top.inputs[0]
            }
            require( top is SNodeNary ) {"sum-product block does not have a product; found $top id=${top.id}"}
            top as SNodeNary
            val product = top.op
            val edges = top.inputs.mapTo(ArrayList(), ::Input)
            return Block(sumBlocks, product, edges)
        }
    }

    // possibly add a Constant subclass

    data class Input(
            val id: Id,
            override val schema: Schema,
            override val nnz: Long?
    ) : SumProduct() {
        constructor(snode: SNode)
                : this(snode.id, Schema(snode.schema), null) // todo fill with nnz estimate

        // Edges are equal if they have the same id.
        override fun equals(other: Any?): Boolean {
             if (this === other) return true
             if (other?.javaClass != javaClass) return false
             other as Input
             return id == other.id
         }
        override fun hashCode() = id.hashCode()
        // Input is immutable
        override fun deepCopy() = this
        override fun toString(): String {
            return "Input($id${if(SHOW_NNZ) ", nnz=$nnz" else ""}):$schema"
        }

    }

    class Block private constructor(
            val sumBlocks: ArrayList<SumBlock>,
            val product: SNodeNary.NaryOp,
            val edges: ArrayList<SumProduct>
    ) : SumProduct() {
        override val nnz: Long? = null // todo compute nnz estimate

        private var _allSchema: Schema? = null
        /** Schema of all attributes, both aggregated and retained. */
        fun allSchema(refresh: Boolean = false): Schema {
            if( refresh || _allSchema == null ) {
                _allSchema = edges.fold(Schema()) { schema, sp ->
                    schema.apply{unionWithBound(sp.schema)} }
            }
            return _allSchema!!
        }

        private var _schema: Schema? = null
        override val schema: Schema
            get() {
                if( _schema == null ) {
                    _schema = Schema(allSchema())
                    _schema!!.removeBoundAttributes(aggNames())
                }
                return _schema!!
            }

        private var _aggSchema: Schema? = null
        /** Schema of aggregated attributes. */
        fun aggSchema(refresh: Boolean = false): Schema {
            if( refresh || _aggSchema == null ) {
                _aggSchema = edges.fold(Schema()) { schema, sp ->
                    schema.apply{unionWithBound(sp.schema.zip().filter { (n,_) ->
                        n in aggNames()
                    }.unzip().let { (ns,ss) -> Schema(ns,ss) })} }
            }
            return _aggSchema!!
        }

        init {
            check(edges.isNotEmpty()) {"Empty inputs to Block $this"}
        }

        override fun toString(): String {
            return "Block$sumBlocks<$product>$edges"+(if(SHOW_NNZ) "(nnz=$nnz)" else "")
        }

        override fun deepCopy() = Block(ArrayList(sumBlocks), product, ArrayList(edges))

        constructor(sumBlocks: Collection<SumBlock>, product: SNodeNary.NaryOp, edges: Collection<SumProduct>)
                : this(ArrayList(sumBlocks), product, ArrayList(edges))
        constructor(sumBlocks: Collection<SumBlock>, product: SNodeNary.NaryOp, vararg edges: SumProduct)
                : this(ArrayList(sumBlocks), product, ArrayList(edges.asList()))
        constructor(sumBlock: SumBlock, product: SNodeNary.NaryOp, edges: Collection<SumProduct>)
                : this(arrayListOf(sumBlock), product, ArrayList(edges))
        constructor(sumBlock: SumBlock, product: SNodeNary.NaryOp, vararg edges: SumProduct)
                : this(arrayListOf(sumBlock), product, ArrayList(edges.asList()))
        constructor(product: SNodeNary.NaryOp, edges: Collection<SumProduct>)
                : this(ArrayList(), product, ArrayList(edges))
        constructor(product: SNodeNary.NaryOp, vararg edges: SumProduct)
                : this(ArrayList<SumBlock>(), product, ArrayList(edges.asList()))

        private var _aggNames: Set<Name>? = null
        fun aggNames(refresh: Boolean = false): Set<Name> {
            if( refresh || _aggNames == null ) {
                _aggNames = sumBlocks.fold(setOf<Name>()) { acc, sb -> acc + sb.names }
            }
            return _aggNames!!
        }

        private var _nameToIncidentEdge: Map<Name,List<SumProduct>>? = null
        /** Map of name to all edges touching that name. */
        fun nameToIncidentEdge(refresh: Boolean = false): Map<Name,List<SumProduct>> {
            if( refresh || _nameToIncidentEdge == null ) {
                _nameToIncidentEdge = edges.flatMap { edge ->
                    edge.schema.names.map { name -> name to edge }
                }.groupBy(Pair<Name,SumProduct>::first).mapValues { (_,v) -> v.map(Pair<Name,SumProduct>::second) }
            }
            return _nameToIncidentEdge!!
        }

        private var _nameToAdjacentNames: Map<Name, Set<Name>>? = null
        /** Map of name to all names adjacent to it via some edge. */
        fun nameToAdjacentNames(refresh: Boolean = false): Map<Name, Set<Name>> {
            if( refresh || _nameToIncidentEdge == null ) {
                _nameToAdjacentNames = nameToIncidentEdge(refresh).mapValues { (_,edges) ->
                    edges.flatMap { it.schema.names }.toSet()
                }
            }
            return _nameToAdjacentNames!!
        }

        private var _edgesGroupByIncidentNames: Map<Set<Name>, List<SumProduct>>? = null
        fun edgesGroupByIncidentNames(refresh: Boolean = false): Map<Set<Name>, List<SumProduct>> {
            if( refresh || _edgesGroupByIncidentNames == null ) {
                _edgesGroupByIncidentNames = edges.groupBy { it.schema.names.toSet() }
            }
            return _edgesGroupByIncidentNames!!
        }

        fun refresh() {
            _schema = null
            _aggNames = null
            _nameToIncidentEdge = null
            _nameToAdjacentNames = null
            _edgesGroupByIncidentNames = null
        }




        fun canAggregate(aggName: Name): Boolean {
            val sumBlockIndex = sumBlocks.indexOfFirst { aggName in it.names }
            require( sumBlockIndex != -1 ) {"no such aggregation over $aggName in $this"}
            val adjacentNames = this.nameToAdjacentNames()[aggName]!!
            // check forward -- all names in future blocks must not be adjacent to aggName
            return (sumBlockIndex+1..sumBlocks.size-1).all { idx ->
                this.sumBlocks[idx].names.all { it !in adjacentNames }
            }
        }

        private fun removeAggName(aggName: Name): Hop.AggOp {
            val idx = sumBlocks.indexOfFirst { aggName in it.names }
            require(idx != -1) {"tried to remove an aggName $aggName that is not being aggregated in $this"}
            val sumBlock = sumBlocks[idx]
            sumBlock.names -= aggName
            if( sumBlock.names.isEmpty() )
                this.sumBlocks.removeAt(idx)
            return sumBlock.op
        }

        private fun addAggNamesToFront(aggOp: Hop.AggOp, vararg aggName: Name) {
            if( sumBlocks.isEmpty() || sumBlocks[0].op != aggOp ) {
                sumBlocks.add(0, SumBlock(aggOp, *aggName))
            } else {
                sumBlocks[0].names.addAll(aggName)
            }
        }

        /**
         * Push aggregations down if they are not join conditions (present in >1 edge).
         * Some aggNames cannot be pushed down. We check if it is correct to change the aggregation order.
         */
        fun pushAggregations() {
            // no refresh on aggNames
            aggNames().forEach { aggName ->
                val incidentEdges = nameToIncidentEdge()[aggName]!!
                if( incidentEdges.size == 1 && canAggregate(aggName) ) {
                    val sumOp = removeAggName(aggName)
                    val edge = incidentEdges[0]
                    when( edge ) {
                        is Block -> edge.addAggNamesToFront(sumOp, aggName)
                        is Input -> {
                            val newBlock = Block(SumBlock(sumOp, aggName), product, edge)
                            this.edges -= edge
                            this.edges += newBlock
                            refresh()
                        }
                    }
                }
            }
        }

    }

    /**
     * Given the top-most SNodeAggregate from which the SumProduct was formed,
     * rewrite the SNodes in the sum-product block to reflect the factorized structure of the SumProduct.
     */
    fun applyToNormalForm(_top: SNode): SNode {
        var top = _top
        while (top is SNodeAggregate) {
            top = top.inputs[0]
        }
        require( top is SNodeNary ) {"sum-product block does not have a product; found $top id=${top.id}"}
        top as SNodeNary
        val origInputs: Map<Id, SNode> = top.inputs.map { it.id to it }.toMap()
        top.inputs.forEach { it.parents.remove(top) } // free the inputs from the multiply

        val newTop: SNode = rConstructSPlan(origInputs)

        SNodeRewriteUtils.rewireAllParentChildReferences(_top, newTop)
        newTop.parents.forEach { it.refreshSchemasUpward() }
        return newTop
    }

    private fun rConstructSPlan(origInputs: Map<Id, SNode>): SNode = when( this ) {
        is Input -> origInputs[this.id]!!
        is Block -> {
            // children are recursively created
            // create an SNodeNary for the product, if there are at least two inputs
            // create an SNodeAggregate for each SumBlock
            val inputNodes = this.edges.map { it.rConstructSPlan(origInputs) }
            val mult = if(inputNodes.size >= 2) SNodeNary(this.product, inputNodes) else inputNodes[0]
            sumBlocks.foldRight(mult) { sumBlock, acc ->
                SNodeAggregate(sumBlock.op, acc, sumBlock.names)
            }
        }
    }

}














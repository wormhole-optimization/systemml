package org.apache.sysml.hops.spoof2.enu

import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.spoof2.plan.disjoint
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.SNodeRewriteUtils


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

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other?.javaClass != javaClass) return false

        other as SumBlock

        if (op != other.op) return false
        if (names != other.names) return false

        return true
    }

    override fun hashCode(): Int {
        var result = op.hashCode()
        result = 31 * result + names.hashCode()
        return result
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

        private val ALLOWED_SUMS = setOf(Hop.AggOp.SUM)
        private val ALLOWED_PRODUCTS = setOf(SNodeNary.NaryOp.MULT)

        fun isSumProductBlock(_top: SNode): Boolean {
            var top = _top
            while (top is SNodeAggregate) {
                if( top.op !in ALLOWED_SUMS)
                    return false
                // no foreign parents below the top agg
                if( top !== _top )//&& top.parents.size > 1 )
                    return false
                top = top.inputs[0]
            }
            if( top !is SNodeNary || top.op !in ALLOWED_PRODUCTS
//                    || top.parents.size > 1 // foreign parent
                    || top.inputs.size <= 2 // too few inputs
                    || top.schema.isEmpty() // all-scalar case
                    )
                return false
            return true
        }

        /** Strips references as it constructs the sum-product block. */
        fun constructBlock(_top: SNode, splitCse: Boolean): Block {
            var top = _top
            val sumBlocks = ArrayList<SumBlock>()
            while (top is SNodeAggregate) {
                sumBlocks += SumBlock(top.op, top.aggreateNames.toMutableSet())
                val topTemp = top
                top = top.inputs[0]
                top.parents -= topTemp
//                if( splitCse && top.parents.size > 1 ) {
//                    // Split CSE
//                    val copy = top.shallowCopyNoParentsYesInputs()
//                    val otherParents = ArrayList(top.parents)
//                    otherParents -= topTemp
//                    top.parents.clear()
//                    top.parents += topTemp
//                    otherParents.forEach {
//                        it.inputs[it.inputs.indexOf(top)] = copy
//                    }
//                    copy.parents.addAll(otherParents)
//                }
            }
            require( top is SNodeNary ) {"sum-product block does not have a product; found $top id=${top.id}"}
            top as SNodeNary
            val product = top.op
            val edges = top.inputs.mapTo(ArrayList(), SumProduct::Input)
            top.inputs.forEach { it.parents -= top }
            return Block(sumBlocks, product, edges)
        }
    }

    open fun toStringWithTab(tab: Int): String = toString()

    // possibly add a Constant subclass

    data class Input(
            val snode: SNode,
            override val schema: Schema,
            override val nnz: Long?
    ) : SumProduct() {

        val baseInput: SNode = if( snode is SNodeBind )
            if( snode.input is SNodeUnbind )
                snode.input.inputs[0]
            else
                snode.input
        else snode

        constructor(snode: SNode)
                : this(snode, Schema(snode.schema), null) // todo fill with nnz estimate

        // Edges are equal if they have the same id.
        override fun equals(other: Any?): Boolean {
             if (this === other) return true
             if (other?.javaClass != javaClass) return false
             other as Input
             return snode == other.snode
         }
        override fun hashCode() = snode.hashCode()
        // Input is immutable
        override fun deepCopy() = this
        override fun toString(): String {
            return "Input($snode${if(SHOW_NNZ) ", nnz=$nnz" else ""}):$schema"
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
//            return "Block$sumBlocks<$product>$edges"+(if(SHOW_NNZ) "(nnz=$nnz)" else "")
//            return "Block$sumBlocks<$product>:\n\t" +
//                    edges.joinToString("\n\t") +(if(SHOW_NNZ) "(nnz=$nnz)" else "")
            return toStringWithTab(1)
        }

        override fun toStringWithTab(tab: Int): String {
            val sep = StringBuilder("\n").let { sb ->
                repeat(tab) {sb.append('\t')}
                sb.toString()
            }
            return "Block$sumBlocks<$product>: $schema" +
                    edges.joinToString(prefix = sep, separator = sep, transform = {it.toStringWithTab(tab+1)}) +(if(SHOW_NNZ) "(nnz=$nnz)" else "")
        }

        override fun deepCopy() = Block(
                sumBlocks.map { it.deepCopy() },
                product,
                edges.map { it.deepCopy() }
        )

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
                }.groupBy(Pair<Name, SumProduct>::first)
                        .mapValues { (n,v) ->
                            v.map(Pair<Name, SumProduct>::second)
                                    // matrix[x,n], vector [n], matrix[n,x]
                                    .sortedBy {
                                        when( it.schema.size ) {
                                            0 -> 0
                                            1 -> 2
                                            else -> if( it.schema.names[0] == n ) 3 else 1
                                        }
                                    }
                        }
            }
            return _nameToIncidentEdge!!
        }

        private var _nameToAdjacentNames: Map<Name, Set<Name>>? = null
        /** Map of name to all names adjacent to it via some edge. */
        fun nameToAdjacentNames(refresh: Boolean = false): Map<Name, Set<Name>> {
            if( refresh || _nameToAdjacentNames == null ) {
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
            _allSchema = null
            _nameToIncidentEdge = null
            _nameToAdjacentNames = null
            _edgesGroupByIncidentNames = null
            _aggSchema = null
        }




        fun factorEdgesToBlock(toMove: Collection<SumProduct>) {
            val groupBlock = Block(this.product, toMove)
            this.edges.removeIf { it in toMove }
            this.edges += groupBlock
            this.refresh()
            this.pushAggregations()
        }

        fun eligibleAggNames(): Set<Name> {
            val (_,eligibleAggs) = sumBlocks.foldRight(setOf<Name>() to setOf<Name>())
            { sumBlock, (aggsSeen, eligibleAggs) ->
                // all names in future blocks must not be adjacent
                (aggsSeen + sumBlock.names) to (eligibleAggs + sumBlock.names.filter { testAggName ->
                    this.nameToAdjacentNames()[testAggName]!!.disjoint(aggsSeen)
                })
            }
            return eligibleAggs
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
                        is Block -> {
                            edge.addAggNamesToFront(sumOp, aggName)
                            edge.refresh()
                        }
                        is Input -> {
                            val newBlock = Block(SumBlock(sumOp, aggName), product, edge)
                            this.edges -= edge
                            this.edges += newBlock
                        }
                    }
                    refresh()
                }
            }
        }

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other?.javaClass != javaClass) return false

            other as Block

            if (sumBlocks != other.sumBlocks) return false
            if (product != other.product) return false
            if (edges != other.edges) return false

            return true
        }

        override fun hashCode(): Int {
            var result = sumBlocks.hashCode()
            result = 31 * result + product.hashCode()
            result = 31 * result + edges.hashCode()
            return result
        }

        internal fun buildAndCostAggs(mult: SNode): SNode {
            return when( this.sumBlocks.size ) {
                0 -> {
                    val cost = SPCost.costFactoredBlock(this, false)
                    mult.cachedCost += cost.multiplyPart()
                    mult
                }
                1 -> {
                    val sumBlock = this.sumBlocks[0]
                    val agg = SNodeAggregate(sumBlock.op, mult, sumBlock.names)
                    val cost = SPCost.costFactoredBlock(this, false)
                    agg.cachedCost = cost.addPart()
                    mult.cachedCost += cost.multiplyPart()
                    agg
                }
                else -> {
                    val spb = SumProduct.Block(this.sumBlocks.subList(1, this.sumBlocks.size), this.product, this.edges)
                    val aggBelow = spb.buildAndCostAggs(mult)
                    val sumBlock = this.sumBlocks[0]
                    val agg = SNodeAggregate(sumBlock.op, aggBelow, sumBlock.names)
                    agg.cachedCost = SPCost.costFactoredBlock(this, false).addPart() - agg.cachedCost
                    agg
                }
            }
        }
    }

    /**
     * Given the top-most SNodeAggregate from which the SumProduct was formed,
     * rewrite the SNodes in the sum-product block to reflect the factorized structure of the SumProduct.
     */
    fun applyToNormalForm(_top: SNode): SNode {
        val newTop: SNode = rConstructSPlan()
        SNodeRewriteUtils.rewireAllParentChildReferences(_top, newTop)
        newTop.parents.forEach { it.refreshSchemasUpward() }
        return newTop
    }

    /**
     * Construct SNodes from this block. Each multiply and agg SNode has a cached cost according to SPCost.
     */
    fun constructSPlan(): SNode = rConstructSPlan()

    private fun rConstructSPlan(): SNode = when( this ) {
        is Input -> this.snode
        is Block -> {
            // children are recursively created
            // create an SNodeNary for the product, if there are at least two inputs
            // create an SNodeAggregate for each SumBlock
            val inputNodes = this.edges.map { it.rConstructSPlan() }
            val mult: SNode = createMultiply(inputNodes)
            buildAndCostAggs(mult) // assigns add costs to each SNAggregate
        }
    }



    private fun createMultiply(inputNodes: List<SNode>): SNode {
        this as Block
        check( inputNodes.isNotEmpty() )
        if(inputNodes.size == 1)
            return inputNodes[0]
        // check for case VMV -- choose which MxV is better to do first
        // if there is no aggregate then it doesn't actually matter, but no harm done
        if( inputNodes.size == 3) {
            val size1count = inputNodes.count { it.schema.size == 1 }
            val size2count = inputNodes.count { it.schema.size == 2 }
            if (size2count == 1 && size1count == 2) {
                val matrix = inputNodes.find { it.schema.size == 2 }!!
                var v1 = inputNodes.find { it.schema.size == 1 }!!
                var v2 = inputNodes.findLast { it.schema.size == 1 }!!
                val s1 = (v1.schema.shapes).first()
                val s2 = (v2.schema.shapes).first()
                if (s1 < s2) // ensure s1 >= s2
                    run { val t = v1; v1 = v2; v2 = t }
                val nary1 = SNodeNary(this.product, matrix, v1) // aggregate will be pushed down
                val nary2 = SNodeNary(this.product, nary1, v2)
                return nary2
            }
            // check for a--x--y case MVM
            // choose whether to multiply the vector with the first or second matrix first.
            if (size1count == 1 && size2count == 2) {
                val vector = inputNodes.find { it.schema.size == 1 }!!
//            val n12 = vector.schema.names.first()
                val s12 = vector.schema.shapes.first()
                var m1 = inputNodes.find { it.schema.size == 2 }!!
                var m2 = inputNodes.findLast { it.schema.size == 2 }!!
                val s1 = (m1.schema.shapes - s12).first()
                val s2 = (m2.schema.shapes - s12).first()
                if (s1 > s2)
                    run { val t = m1; m1 = m2; m2 = t }
                val nary1 = SNodeNary(this.product, m1, vector)
                val nary2 = SNodeNary(this.product, nary1, m2)
                return nary2
            }
        }
        return SNodeNary(this.product, inputNodes)
    }

    fun recUnionSchema(rSchema: Schema = Schema()): Schema {
        when( this ) {
            is Input -> rSchema.unionWithBound(this.schema)
            is Block -> this.edges.forEach { it.recUnionSchema(rSchema) }
        }
        return rSchema
    }

    fun getAllInputs(): Set<SNode> = mutableSetOf<SNode>().let { getAllInputs(it); it }
    private fun getAllInputs(inputs: MutableSet<SNode>) {
        when(this) {
            is Input -> inputs += snode
            is Block -> this.edges.forEach { it.getAllInputs(inputs) }
        }
    }

    fun countAggsAndInternalBlocks(): Int = when(this) {
        is Input -> 0
        is Block -> this.sumBlocks.size + 1 + this.edges.sumBy { it.countAggsAndInternalBlocks() }
    }

}














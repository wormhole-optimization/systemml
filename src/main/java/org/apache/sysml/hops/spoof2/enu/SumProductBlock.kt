package org.apache.sysml.hops.spoof2.enu

import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.spoof2.plan.disjoint
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.SNodeRewriteUtils


private const val SHOW_NNZ = false


class SumBlock private constructor(
        val op: Hop.AggOp,
        val names: Schema
) {
    constructor(sum: Hop.AggOp, names: Collection<Pair<AB,Shape>>)
            : this(sum, Schema(names))
    constructor(sum: Hop.AggOp, vararg names: Pair<AB,Shape>)
            : this(sum, Schema(names.asList()))
    companion object {
        operator fun invoke(op: Hop.AggOp, schema: Schema) = SumBlock(op, Schema(schema))
    }
    fun deepCopy() = SumBlock(op, Schema(names))
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
        private val ALLOWED_PRODUCTS = setOf(SNodeNary.NaryOp.MULT, SNodeNary.NaryOp.PLUS)

        fun isSumProductBlock(_top: SNode): Boolean {
            var top = _top
            while (top is SNodeAggregate) {
                if( top.op !in ALLOWED_SUMS)
                    return false
                if( top !== _top )//&& top.parents.size > 1 )
                    return false
                top = top.inputs[0]
            }
            if( top !is SNodeNary || top.op !in ALLOWED_PRODUCTS
//                    || top.parents.size > 1 // foreign parent
                    || top.inputs.size <= 1 // too few inputs
                    || top.schema.isEmpty() // all-scalar case
                    )
                return false
            return true
        }

        /** Strips references as it constructs the sum-product block. */
        fun constructBlock(_top: SNode, initialParentForSplitCse: SNode): Block {
            var top = _top
            var topTemp = initialParentForSplitCse
            val sumBlocks = ArrayList<SumBlock>()
            while (top is SNodeAggregate) {
                sumBlocks += SumBlock(top.op, top.aggs)
                topTemp = top
                top = top.inputs[0]
                splitOtherParents(topTemp, top)
            }
            require( top is SNodeNary ) {"sum-product block does not have a product; found $top id=${top.id}"}
            top as SNodeNary
            if( top !== _top )
                splitOtherParents(topTemp, top)
            val edges = top.inputs.mapTo(ArrayList()) { child ->
                if( child is SNodeNary && child.op in ALLOWED_PRODUCTS && child.inputs.size >= 2 && child.schema.isNotEmpty() ) {
                    splitOtherParents(top, child)
                    child.inputs.forEach { it.parents -= child }
                    SPB(child.op, child.inputs.map(::SPI))
                } else {
                    child.parents -= top
                    SPI(child)
                }
            }
            return Block(sumBlocks, top.op, edges)
        }
        private fun splitOtherParents(desiredParent: SNode, node: SNode) {
            node.parents -= desiredParent
            if( node.parents.isNotEmpty() ) {
                val copy = node.shallowCopyNoParentsYesInputs()
                node.parents.forEach {
                    it.inputs[it.inputs.indexOf(node)] = copy
                }
                copy.parents.addAll(node.parents)
                node.parents.clear()
            }
        }

    }

    open fun toStringWithTab(tab: Int): String = toString()
    abstract fun toString_TSVFriendly(): String

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
            return "Input<${snode.id}>($snode${if(SHOW_NNZ) ", nnz=$nnz" else ""}):$schema"
        }

        override fun toString_TSVFriendly(): String {
            val ss = when(snode) {
                is SNodeBind -> "bi(${snode.id})"
                is SNodeUnbind -> "ub(${snode.id})"
                is SNodeData -> if( snode.isLiteral ) snode.literalDouble.toString() else snode.toString()
                else -> snode.toString()
            }
            return "$ss:${schema.names}"
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
                    schema += sp.schema; schema
            } }
            return _allSchema!!
        }

        private var _schema: Schema? = null
        override val schema: Schema
            get() {
                if( _schema == null ) {
                    _schema = Schema(allSchema())
                    _schema!! -= aggNames()
                }
                return _schema!!
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
        override fun toString_TSVFriendly(): String {
            return "Block$sumBlocks<$product>[${edges.joinToString { it.toString_TSVFriendly() }}]"
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

        fun aggSchemaNotInEdges(): Schema {
            return aggSchema().filter { n, _ -> edges.none { n in it.schema } }
        }

        private var _aggSchema: Schema? = null
        @Suppress("UNCHECKED_CAST")
        fun aggSchema(refresh: Boolean = false): Schema {
            if( refresh || _aggSchema == null ) {
                _aggSchema = sumBlocks.fold(Schema()) { acc, sb -> acc += sb.names; acc }
            }
            return _aggSchema!!
        }
        fun aggNames(refresh: Boolean = false): Set<AB> = aggSchema(refresh).map { (n,_) -> n as AB }.toSet()

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
                                            else -> if( it.schema.names.first() == n ) 3 else 1
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
            _aggSchema = null
            _allSchema = null
            _nameToIncidentEdge = null
            _nameToAdjacentNames = null
            _edgesGroupByIncidentNames = null
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
                (aggsSeen + sumBlock.names.names) to (eligibleAggs + sumBlock.names.names.filter { testAggName ->
                    this.nameToAdjacentNames()[testAggName]!!.disjoint(aggsSeen)
                })
            }
            return eligibleAggs
        }

        fun canAggregate(aggName: AB): Boolean {
            val sumBlockIndex = sumBlocks.indexOfFirst { aggName in it.names }
            require( sumBlockIndex != -1 ) {"no such aggregation over $aggName in $this"}
            val adjacentNames = this.nameToAdjacentNames()[aggName]!!
            // check forward -- all names in future blocks must not be adjacent to aggName
            return (sumBlockIndex+1..sumBlocks.size-1).all { idx ->
                this.sumBlocks[idx].names.names.all { it !in adjacentNames }
            }
        }

        private fun removeAggName(aggName: AB): Hop.AggOp {
            val idx = sumBlocks.indexOfFirst { aggName in it.names }
            require(idx != -1) {"tried to remove an aggName $aggName that is not being aggregated in $this"}
            val sumBlock = sumBlocks[idx]
            sumBlock.names -= aggName
            if( sumBlock.names.isEmpty() )
                this.sumBlocks.removeAt(idx)
            return sumBlock.op
        }

        private fun addAggNamesToFront(aggOp: Hop.AggOp, vararg agg: Pair<AB,Shape>) {
            if( sumBlocks.isEmpty() || sumBlocks[0].op != aggOp ) {
                sumBlocks.add(0, SumBlock(aggOp, agg.asList()))
            } else {
                sumBlocks[0].names += agg
            }
        }

        /**
         * Push aggregations down if they are not join conditions (present in >1 edge).
         * Some aggNames cannot be pushed down. We check if it is correct to change the aggregation order.
         */
        fun pushAggregations() {
            // no refresh on aggNames
            aggSchema().forEach { (aggName, shape) ->
                aggName as AB
                if( aggName in allSchema() ) {
                    val incidentEdges = nameToIncidentEdge()[aggName]!!
                    if (incidentEdges.size == 1 && canAggregate(aggName)) {
                        val sumOp = removeAggName(aggName)
                        val edge = incidentEdges[0]
                        when (edge) {
                            is Block -> {
                                edge.addAggNamesToFront(sumOp, aggName to shape)
                                edge.refresh()
                            }
                            is Input -> {
                                val newBlock = Block(SumBlock(sumOp, aggName to shape), product, edge)
                                this.edges -= edge
                                this.edges += newBlock
                            }
                        }
                        refresh()
                    }
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

        internal fun buildAndCostAggs(mult: SNode, doCost: Boolean): SNode {
            return when( this.sumBlocks.size ) {
                0 -> {
                    if( doCost ) {
                        val cost = SPCost.costFactoredBlock(this, false)
                        mult.cachedCost += cost.multiplyPart()
                    }
                    mult
                }
                1 -> {
                    val sumBlock = this.sumBlocks[0]
                    val agg = SNodeAggregate(sumBlock.op, mult, sumBlock.names)
                    if( doCost ) {
                        val cost = SPCost.costFactoredBlock(this, false)
                        agg.cachedCost = cost.addPart()
                        mult.cachedCost += cost.multiplyPart()
                    }
                    agg
                }
                else -> {
                    val spb = SumProduct.Block(this.sumBlocks.subList(1, this.sumBlocks.size), this.product, this.edges)
                    val aggBelow = spb.buildAndCostAggs(mult, doCost)
                    val sumBlock = this.sumBlocks[0]
                    val agg = SNodeAggregate(sumBlock.op, aggBelow, sumBlock.names)
                    if( doCost )
                        agg.cachedCost = SPCost.costFactoredBlock(this, false).addPart() - agg.cachedCost
                    agg
                }
            }
        }

        fun unionInSumBlocks(sums: List<SumBlock>) {
            sums.forEach { sum ->
                val sb = sumBlocks.find { it.op == sum.op } ?: SumBlock(sum.op).also { sumBlocks += it }
                sb.names += sum.names
            }
        }

        fun constructNoRec(inputNodes: List<SNode>, cost: Boolean = true): SNode {
            val mult: SNode = createMultiply(inputNodes)
            return buildAndCostAggs(mult, cost) // assigns add costs to each SNAggregate
        }

        fun removeAggs(toRemove: Schema) {
            val iter = sumBlocks.iterator()
            while( iter.hasNext() ) {
                val sb = iter.next()
                sb.names -= toRemove
                if( sb.names.isEmpty() )
                    iter.remove()
            }
        }
    }

    class EBlock(
            val blocks: List<SumProduct>
    ) : SumProduct() {
        init {
            check(blocks.isNotEmpty())
        }
        var nextBlock = 0

        override val schema = blocks[0].schema
        override val nnz = blocks[0].nnz
        override fun deepCopy() = EBlock(blocks.map(SumProduct::deepCopy))
        override fun toString_TSVFriendly(): String {
            return "EBlock(${blocks.map { it.toString_TSVFriendly() }})"
        }
        override fun toString(): String {
            return toStringWithTab(1)
        }
        override fun toStringWithTab(tab: Int): String {
            val sep = StringBuilder(",\n").let { sb ->
                repeat(tab) {sb.append('\t')}
                sb.toString()
            }
            return "EBlock{" +
                    blocks.joinToString(prefix = sep.substring(1,sep.length), separator = sep, transform = {it.toStringWithTab(tab+1)}, postfix = "}")
        }
    }

    /**
     * Given the top-most SNodeAggregate from which the SumProduct was formed,
     * rewrite the SNodes in the sum-product block to reflect the factorized structure of the SumProduct.
     */
    fun applyToNormalForm(_top: SNode, cost: Boolean = true, factor: Boolean = true): SNode {
        val newTop: SNode = rConstructSPlan(cost, factor)
        SNodeRewriteUtils.rewireAllParentChildReferences(_top, newTop)
        newTop.parents.forEach { it.refreshSchemasUpward() }
        return newTop
    }

    /**
     * Construct SNodes from this block. Each multiply and agg SNode has a cached cost according to SPCost.
     */
    fun constructSPlan(cost: Boolean = true): SNode = rConstructSPlan()

    private fun rConstructSPlan(cost: Boolean = true, factor: Boolean = true): SNode = when( this ) {
        is Input -> this.snode
        is Block -> {
            // children are recursively created
            // create an SNodeNary for the product, if there are at least two inputs
            // create an SNodeAggregate for each SumBlock
            val inputNodes = this.edges.map { it.rConstructSPlan(cost, factor) }
            val mult: SNode = createMultiply(inputNodes, factor)
            buildAndCostAggs(mult, cost) // assigns add costs to each SNAggregate
        }
        is ESP -> throw IllegalStateException("unexpected EBlock")
    }


    internal fun createMultiply(inputNodes: List<SNode>, factor: Boolean = true): SNode {
        this as Block
        check( inputNodes.isNotEmpty() )
        if(inputNodes.size == 1)
            return inputNodes[0]
        if( this.product == SNodeNary.NaryOp.PLUS ) // todo: maybe change order of inputs to add scalars first, then vectors, then matrices
            return SNodeNary(this.product, inputNodes)
        // check for case VMV -- choose which MxV is better to do first
        // if there is no aggregate then it doesn't actually matter, but no harm done
        if( factor && inputNodes.size == 3) {
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
            is Input -> rSchema += this.schema
            is Block -> this.edges.forEach { it.recUnionSchema(rSchema) }
        }
        return rSchema
    }

    fun getAllInputs(): List<SNode> = mutableListOf<SNode>().let { getAllInputs(it); it }
    private fun getAllInputs(inputs: MutableList<SNode>) {
        when(this) {
            is Input -> inputs += snode
            is Block -> this.edges.forEach { it.getAllInputs(inputs) }
        }
    }

    fun countAggsAndInternalBlocks(): Int = when(this) {
        is Input -> 0
        is Block -> this.sumBlocks.size + 1 + this.edges.sumBy { it.countAggsAndInternalBlocks() }
        is ESP -> throw IllegalStateException("unexpected EBlock")
    }

}














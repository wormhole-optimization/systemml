package org.apache.sysml.hops.spoof2.enu

import org.apache.commons.logging.LogFactory
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
        private const val SPLIT_BU_SPBLOCK = true
        private val ALLOWED_SUMS = setOf(Hop.AggOp.SUM)
        private val ALLOWED_PRODUCTS = setOf(SNodeNary.NaryOp.MULT, SNodeNary.NaryOp.PLUS)

        internal fun COND_PRODUCT(top: SNode, acceptNoSchema: Boolean = false) = top is SNodeNary && top.op in ALLOWED_PRODUCTS
//                    && top.parents.size == 1 // foreign parent
                && (acceptNoSchema || top.schema.isNotEmpty()) // all-scalar case

        internal tailrec fun COND_AGG(top: SNode, numAggsBefore: Int = 0): Boolean {
            return if( top is SNodeAggregate ) {
                if(top.op in ALLOWED_SUMS
                        && numAggsBefore == 0) // currently no support for >1 aggregate type
                    COND_AGG(top.input, numAggsBefore+1)
                else false
            } else COND_PRODUCT(top)
        }

        fun isSumProductBlock(_top: SNode): Boolean {
            return COND_AGG(_top)
        }

        /** Strips references as it constructs the sum-product block. */
        fun constructBlock(_top: SNode, initialParentForSplitCse: SNode): SumProduct {
            return constructBlock(_top, initialParentForSplitCse, true)
        }

        // requires that RewriteSplitBU_ExtendNormalForm ran previously,
        // or else the normal form will not be as large as it could be due to binds blocking the way
        fun constructBlock(_top: SNode, initialParentForSplitCse: SNode, first: Boolean, collectedInputs: MutableSet<SNode> = hashSetOf()): SumProduct {
            var top = _top
            var topTemp = initialParentForSplitCse
            if( !COND_PRODUCT(getBelowAgg(top)) ) {
                top.parents -= topTemp
                collectedInputs += top
                return SPI(top)
            }
            if( !first )
                splitOtherParents(topTemp, top)
            val sumBlocks = ArrayList<SumBlock>()
            while (top is SNodeAggregate) {
                sumBlocks += SumBlock(top.op, top.aggs)
                topTemp = top
                top = top.inputs[0]
                splitOtherParents(topTemp, top)
            }
            top as SNodeNary
            val (newSumBlocks, edges) = top.inputs.map { child ->
                val x = constructBlock(child, top, false, collectedInputs)
                if( x is Block && x.product == (top as SNodeNary).op ) {
                    x.sumBlocks to x.edges
                } else listOf<SumBlock>() to listOf(x)
            }.unzip().let { (sbs,es) ->
                // The splitBindBelowAgg code renames ALL aggregated names, which makes this correct. This is conservative; some names will be renamed that needn't have been.
                sbs.flatten() to es.flatten()
            }
            return Block(sumBlocks, top.op, edges).apply { unionInSumBlocks(newSumBlocks) }
        }

        private fun splitBindBelowAgg(top: SNode, aboveTop: SNode, collectedInputs: Set<SNode>): SNode {
            val (bind, aboveBind) = getBelowAgg(top, aboveTop)
            if( bind is SNodeBind && bind.input is SNodeUnbind ) {
                val unbind = bind.input as SNodeUnbind
                val below = getBelowAgg(unbind.input)
                if( COND_PRODUCT(below) ) {
                    // rename below the unbind from the unbind atts to the bind atts
                    val renaming: Map<AB, AB> = unbind.unbindings.zipIntersect(bind.bindings).values.toMap()
                    LogFactory.getLog(SumProduct::class.java)!!.debug("renaming is $renaming on unbind input ${unbind.input} ${unbind.input.schema}")
                    val newUnbindInput = unbind.input.renameCopyDown(renaming)
                    bind.parents -= aboveBind
                    stripDead(bind, collectedInputs)
                    // move aboveBind's input from bind to newUnbindInput
                    do {
                        aboveBind.inputs[aboveBind.inputs.indexOf(bind)] = newUnbindInput
                        newUnbindInput.parents += aboveBind
                    } while (aboveBind.inputs.indexOf(bind) != -1)
                    aboveBind.refreshSchemasUpward()
                    return newUnbindInput
                }
            }
            return top
        }

        internal tailrec fun getBelowAgg(node: SNode): SNode =
                if( node is SNodeAggregate && node.op in ALLOWED_SUMS ) getBelowAgg(node.input) else node
        internal tailrec fun getBelowAgg(node: SNode, aboveNode: SNode): Pair<SNode,SNode> =
                if( node is SNodeAggregate && node.op in ALLOWED_SUMS ) getBelowAgg(node.input, node) else node to aboveNode
        internal fun getBelowAggPlusMult(node: SNode): Set<SNode> {
            val set = mutableSetOf<SNode>()
            getBelowAggPlusMult(getBelowAgg(node), set)
            return set
        }
        private fun getBelowAggPlusMult(node: SNode, set: MutableSet<SNode>) {
            if( COND_PRODUCT(node, true) ) {
                node.inputs.toSet().forEach { getBelowAggPlusMult(getBelowAgg(it), set) }
            } else {
                set += node
            }
        }

        private fun splitOtherParents(desiredParent: SNode, node: SNode) {
            node.parents -= desiredParent
            if( node.parents.isNotEmpty() ) {
                val copy = node.shallowCopyNoParentsYesInputs()
                node.parents.forEach {
                    it.inputs[it.inputs.lastIndexOf(node)] = copy
                }
                copy.parents.addAll(node.parents)
                node.parents.clear()
                stripDead(node)
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

        val baseInput: SNode =
                if( snode is SNodeBind )
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
            return "Input<${snode.id}${if(baseInput != snode) ":${baseInput.id}" else ""}>($snode${if(SHOW_NNZ) ", nnz=$nnz" else ""}):$schema"
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

        // return null if any node has cost infinity
        internal fun buildAndCostAggs(mult: SNode, doCost: Boolean): SNode? {
            return when( this.sumBlocks.size ) {
                0 -> {
                    if( doCost ) {
                        val cost = SPCost.costFactoredBlock(this, false)
                        if(cost.exceedsMaxCost()) return null
                        mult.cachedCost += cost.multiplyPart()
                    }
                    mult
                }
                1 -> {
                    val sumBlock = this.sumBlocks[0]
                    val agg = SNodeAggregate(sumBlock.op, mult, sumBlock.names)
                    if( doCost ) {
                        val cost = SPCost.costFactoredBlock(this, false)
                        if(cost.exceedsMaxCost()) return null
                        agg.cachedCost = cost.addPart()
                        mult.cachedCost += cost.multiplyPart()
                    }
                    agg
                }
                else -> {
                    val spb = SumProduct.Block(this.sumBlocks.subList(1, this.sumBlocks.size), this.product, this.edges)
                    val aggBelow = spb.buildAndCostAggs(mult, doCost) ?: return null
                    val sumBlock = this.sumBlocks[0]
                    val agg = SNodeAggregate(sumBlock.op, aggBelow, sumBlock.names)
                    if( doCost ) {
                        val cost = SPCost.costFactoredBlock(this, false)
                        if(cost.exceedsMaxCost()) return null
                        agg.cachedCost = cost.addPart() - agg.cachedCost
                    }
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

        fun constructNoRec(inputNodes: List<SNode>, cost: Boolean = true): SNode? {
            val mult: SNode = createMultiply(inputNodes)
            val agg = buildAndCostAggs(mult, cost) // assigns add costs to each SNAggregate
            if( agg == null )
                stripDead(mult, getBelowAggPlusMult(mult)) //getAllInputs().toSet()
            return agg
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
    fun applyToNormalForm(_top: SNode, cost: Boolean = true, factor: Boolean = true): SNode? {
        val newTop = rConstructSPlan(cost, factor) ?: return null
        SNodeRewriteUtils.rewireAllParentChildReferences(_top, newTop)
        newTop.parents.forEach { it.refreshSchemasUpward() }
        return newTop
    }

    /**
     * Construct SNodes from this block. Each multiply and agg SNode has a cached cost according to SPCost.
     */
    fun constructSPlan(cost: Boolean = true): SNode? = rConstructSPlan()

    private fun rConstructSPlan(cost: Boolean = true, factor: Boolean = true): SNode? = when( this ) {
        is Input -> this.snode
        is Block -> {
            // children are recursively created
            // create an SNodeNary for the product, if there are at least two inputs
            // create an SNodeAggregate for each SumBlock
            val inputNodes = this.edges.map { it.rConstructSPlan(cost, factor) ?: return null }
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
    fun getAllInputBlocks(): List<SPI> = mutableListOf<SPI>().let { getAllInputBlocks(it); it }
    private fun getAllInputBlocks(inputs: MutableList<SPI>) {
        when(this) {
            is Input -> inputs += this
            is Block -> this.edges.forEach { it.getAllInputBlocks(inputs) }
        }
    }

    fun countAggsAndInternalBlocks(): Int = when(this) {
        is Input -> 0
        is Block -> this.sumBlocks.size + 1 + this.edges.sumBy { it.countAggsAndInternalBlocks() }
        is ESP -> throw IllegalStateException("unexpected EBlock")
    }
}














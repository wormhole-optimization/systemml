package org.apache.sysml.hops.spoof2.enu2

import org.apache.commons.logging.LogFactory
import org.apache.log4j.Level
import org.apache.log4j.Logger
import org.apache.sysml.conf.DMLConfig
import org.apache.sysml.hops.DataOp
import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.SNodeRewriteUtils
import org.apache.sysml.runtime.controlprogram.parfor.util.IDSequence


typealias ABList = List<AB>
typealias ShapeList = List<Shape>
private fun ShapeList.toUnboundSchema(): Schema = Schema(this.mapIndexed { i, s -> AU(i) as Name to s })


sealed class Construct(
        val buo: BottomUpOptimize,
        val children: List<Construct>,
        val nnz: Nnz,
        val thisCost: Double,
        val outer: ShapeList
) {
    val outerSchema = outer.toUnboundSchema() //Schema(outer.mapIndexed { i, s -> AU(i) as Name to s })

    override fun toString(): String {
        return "${javaClass.simpleName}$children" // <p:${parents.size}>
    }

    val id: Id = _idSeq.nextID
    val height: Int // = if (children.isEmpty()) 0 else children.maxBy { it.height }!!.height + 1
    init { height = 1 + (children.maxBy { it.height }?.height ?: -1) }

    val recConstructsNoSelf: Set<Construct>
    val recCost: Double
    /** Used for "local" pruning: if cost, discounting those sub-operations that can be shared,
    * exceeds another alternative's cost, then prune.
    * Does not change as long as children are fully constructed */
    val recCostNoShare: Double
    /** Sum of nnz of bases included in this construct. Used as a heuristic in `recCostNoShare / coveredEdgeWeight`. */
    val coveredBaseNnzSum: Nnz

    init {
        val rc = children.flatMap { it.recConstructsNoSelf + it }.toSet()
        var recCost = thisCost
        var recCostNoShare = thisCost
        var coveredBaseNnzSum = if (height == 0) nnz else 0L
        for (c in rc) {
            recCost += c.thisCost
            recCostNoShare = (2 - c.cmaps.map { it.tgtGraph }.toSet().size) * c.thisCost
            if (c.height == 0)
                coveredBaseNnzSum += c.nnz
        }
        this.recCost = recCost //rc.sumByDouble { it.thisCost } + thisCost
        this.recCostNoShare = recCostNoShare //rc.sumByDouble { c -> (2 - c.cmaps.map { it.tgtGraph }.toSet().size) * c.thisCost } + thisCost
        this.coveredBaseNnzSum = coveredBaseNnzSum
        recConstructsNoSelf = rc
    }

    val cmaps: MutableList<CMap> = mutableListOf()


    abstract fun fillCMaps()


    // if we re-enable this, then make sure pruned contructs are removed from the parents of their children
    val parents: MutableList<Construct> = mutableListOf()
    init { children.forEach { it.parents += this } }

    fun makeAlignedEMultAbove(buo: BottomUpOptimize, c2: Construct): EWiseMult = makeEMultAbove(buo, c2, true)

    fun makeEMultAbove(buo: BottomUpOptimize, c2: Construct, aligned: Boolean): EWiseMult {
        return parents.find {
            it is EWiseMult && (it.a == c2 && it.b === this || it.b == c2 && it.a === this) && it.aligned == aligned
        } as? EWiseMult ?: EWiseMult.construct(buo, this, c2, aligned)
    }

    fun makePlusAbove(buo: BottomUpOptimize, c2: Construct): Plus {
        return parents.find {
            it is Plus && (it.a == c2 && it.b === this || it.b == c2 && it.a === this)
        } as? Plus ?: Plus.construct(buo, this, c2)
    }

    fun makeOuterAbove(buo: BottomUpOptimize, c2: Construct): Outer {
        // determine orientation in the Outer.construct method
        return parents.find {
            it is Outer && (it.a == c2 && it.b === this || it.b == c2 && it.a === this)
        } as? Outer ?: Outer.construct(buo, this, c2)
    }

    fun makeRenameAbove(buo: BottomUpOptimize, schema: ABList): Rename {
        return parents.find { it is Rename && it.schema == schema }
                as? Rename ?: Rename(buo, this, schema)
    }

    fun makeMxMAbove(buo: BottomUpOptimize, c2: Construct, aj: Int, bj: Int): MatrixMult {
        return parents.find { it ->
            when {
                it !is MatrixMult -> false
                c2 == this && it.a == this && it.b == this -> it.type.aj == bj && it.type.bj == aj || it.type.aj == aj && it.type.bj == bj
                it.a == c2 -> it.type.aj == bj && it.type.bj == aj
                it.b == c2 -> it.type.aj == aj && it.type.bj == bj
                else -> false
            }
        } as? MatrixMult ?: MatrixMult.construct(buo, this, c2, aj, bj)
    }

    fun makeAggAbove(buo: BottomUpOptimize, pos: Int): Agg {
        return parents.find { it is Agg && it.aggPos == pos }
                as? Agg ?: Agg.construct(buo, this, pos)
    }



    // if non-null, then all alternative constructs (semantically equivalent) have the same mutable set with themselves inside
    var siblings: MutableSet<Construct>? = null

    fun isLocallyPruned(siblings: Collection<Construct>? = this.siblings): Boolean {
        val sa = siblings ?: return false
        // for each alternative to this construct,
        // check whether the recCostNoShare of c is greater than that of the alternative. If so, prune.
        if (BottomUpOptimize.PRUNE_FULLY_LOCAL) {
            for (a in sa)
                if (recCost > a.recCost)
                    return true
        } else {
            for (a in sa)
                if (recCostNoShare > a.recCost)
                    return true
        }
        return false
    }


    private var cachedSNode: Pair<SNode, ABList>? = null

    fun convertToSNode(): Pair<SNode, ABList> { // returned list matches order of outer and order of all cmaps' vertMaps.
        return cachedSNode ?: run {
            val inputs = children.map { it.convertToSNode() }
            val c = _convertToSNode(inputs)
            val r = c
//                if (c.schema.isEmpty() || cmaps.isEmpty()) c
//                else {
//                    val pc = SHash.createAttributePositionList(c, memoAttrPosList)
//                    val rep = cmaps.first()
//                    makeRenameAbove(c, pc.zip(rep.vertMap).map { (x, y) -> x to y.a }.toMap())
//                }
            cachedSNode = r
            r
        }
    }

    // rename the inputs as necessary to apply the construct and obtain an output suitable for rep
    protected abstract fun _convertToSNode(inputs: List<Pair<SNode, ABList>>): Pair<SNode, ABList>



    enum class Status {
        NONE,
        FRONTIER,
        EXPLORED, // either complete or incomplete
        FINAL_MULT,
        FINAL_PLUS,
        FINAL_MULT_PLUS,
        PRUNED;
    }
    var status: Status = Status.NONE

    init {
        buo.costQueue += this
        buo.stats.logCreatedConstruct()
    }


    fun prune() {
        siblings?.remove(this)
        siblings = null
        buo.costQueue.remove(this)
        when (status) {
            Status.NONE -> {}
            Status.FRONTIER -> buo.frontier.remove(this)
            Status.EXPLORED -> {
                cmaps.forEach { cmap ->
                    if (cmap.complete) {
                        val above = this.makeRenameAbove(buo, cmap.vertMap.map(ABS::a))
                        val idx = buo.tgs.invComplete[cmap.tgtGraph].indexOf(above)
                        buo.tgs.invComplete[cmap.tgtGraph].removeAt(idx)
                    } else {
                        val im = buo.tgs.invMaps[cmap.tgtGraph]
                        cmap.vertMap.forEach { v ->
                            im[v]!!.remove(cmap)
                        }
                    }
                }
            }
            // a bit of overkill, because it is a pain to filter to just those that contain this construct
            Status.FINAL_MULT -> buo.tgs.invCompleteMult.forEach { it.remove(this) }
            Status.FINAL_PLUS -> buo.tgs.invCompletePlus.forEach { it.remove(this) }
            Status.FINAL_MULT_PLUS -> {
                buo.tgs.invCompleteMult.forEach { it.remove(this) }
                buo.tgs.invCompletePlus.forEach { it.remove(this) }
            }
            Status.PRUNED -> {}
        }
        while (parents.isNotEmpty())
            parents.last().prune()
        children.forEach { it.parents.remove(this) }
        status = Status.PRUNED
        buo.stats.logPrunedConstruct(recCost >= buo.tgs.upperBound) // local or global
    }

    fun isGlobalPruned(): Boolean {
        return recCost > buo.tgs.upperBound // recCost != buo.tgs.upperBound && recCost > buo.tgs.upperBound - TargetGraphs.COST_EPS
    }

    fun isPruned(): Boolean { if (this is Base) return false
        if (isGlobalPruned())
            return true
        if (cmaps.isEmpty() && siblings == null)
            return false
        val completeSiblings = cmaps.filter { it.complete }.flatMap { completeCMap ->
            val siblings = buo.tgs.invComplete[completeCMap.tgtGraph]
            siblings
        }.toSet()
        val allSiblings = (completeSiblings + (siblings ?: emptySet()))
        return isLocallyPruned(allSiblings)
    }



    companion object {
        private val _idSeq = IDSequence()
        protected val nnzInferer: NnzInferer = WorstCaseNnz
        private val LOG = LogFactory.getLog(Construct::class.java)!!
        private const val LDEBUG = DMLConfig.SPOOF_DEBUG
        init {
            if (LDEBUG) Logger.getLogger(Construct::class.java).level = Level.TRACE
        }

        // order the inputs
        protected fun orderAB(a: Construct, b: Construct): Pair<Construct,Construct> {
            // compare by dim (matrices before vectors), then nnz (denser first), then id (smallest first)
            return when {
                a.outer.size != b.outer.size -> if (a.outer.size >= b.outer.size) a to b else b to a
                a.nnz != b.nnz -> if (a.nnz >= b.nnz) a to b else b to a
                else -> if (a.id <= b.id) a to b else b to a
            }
        }
    }


    class Base private constructor(buo: BottomUpOptimize, val base: SNode, nnz: Nnz, shapeSchema: ShapeList)
        : Construct(buo, listOf(), nnz, 0.0, shapeSchema) {

        override fun toString(): String {
            if (base is SNodeData && base.hop is DataOp
                    && base.hop.isRead
                    && base.hop.dataOpType == Hop.DataOpTypes.TRANSIENTREAD
                    && base.hop.name != null)
                return "Base(${base.hop.name})" // ${base.hop.hopID}@
            return "Base($base)"
        }

        companion object {
            fun Scalar(buo: BottomUpOptimize, base: SNode): Base {
                val nnz = if (SNodeRewriteUtils.isLiteralOfValue(base, 0.0)) 0L else 1L
                return Base(buo, base, nnz, listOf())
            }

            fun NonScalar(buo: BottomUpOptimize, edge: Edge.C, nnz: Nnz, tgs: TargetGraphs): Base {
                // fill with CMaps
                val b = Base(buo, edge.base, nnz, edge.verts.map { it.s })
                tgs.tgtEdgeListNoScalars.withIndex().forEach { (tgi, tg) ->
                    tg.withIndex().filter { (_,e) -> e.base == edge.base }.forEach { (ei,e) ->
                        val ou = if (e.verts.size == 2 && e.verts[0].s != b.outer[0]) e.verts.reversed() else e.verts
                        val coveredEdges = BooleanArray(tg.size)
                        coveredEdges[ei] = true
                        b.cmaps += CMap(b, tgi, ou, coveredEdges)
                    }
                }
                return b
            }
        }

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (javaClass != other?.javaClass) return false

            other as Base

            if (base != other.base) return false

            return true
        }
        override fun hashCode(): Int {
            return base.hashCode()
        }

        override fun fillCMaps() {
            // already filled in
        }

        override fun _convertToSNode(inputs: List<Pair<SNode, ABList>>): Pair<SNode, ABList> {
            if (base.schema.isEmpty())
                return base to listOf()
            // attempt smart binding selection, to reduce the number of renames
            val bindings =
                    if (cmaps.isEmpty()) base.schema.genAllBindings()
                    else cmaps.first().vertMap.mapIndexed { i, (a,_) -> AU(i) to a }.toMap()
            val orderedSchema = bindings.toList().sortedBy { (au, _) -> au.dim }.map { (_, ab) -> ab }
            return makeBindAbove(base, bindings) to orderedSchema
        }
    }


    /**
     * If [aligned]:
     * 1. MeM Aij * Bij
     * 2. MeV Aij * vj
     * 3. VeV vi * wi
     * 4. Multiply by scalar
     *
     * If not aligned:
     * 1. MeMT Aij * Bji
     * 2. VeM Aij * vi
     */
    class EWiseMult private constructor(
            buo: BottomUpOptimize, val a: Construct, val b: Construct, nnz: Nnz, thisCost: Double, val aligned: Boolean
    ) : Construct(buo, listOf(a, b), nnz, thisCost, a.outer) {
        init {
            if (aligned) {
                when (a.outer.size) {
                    2 -> when (b.outer.size) {
                        2 -> require(a.outer == b.outer) {"MeM ewise mult on different outer schemas? $a, $b"}
                        1 -> require(a.outer[1] == b.outer[0]) {"matrix-vector element-wise multiply does not match shapes? $a, $b"}
                    }
                    1 -> if (b.outer.size == 1)
                        require(a.outer[0] == b.outer[0]) {"vector-vector element-wise multiply does not match shape. $a, $b"}
                }
            } else {
                require(a.outer.size == 2) {"Reversed only applies when the left input is a matrix. $a, $b"}
                when (b.outer.size) {
                    2 -> require(a.outer == b.outer.reversed()) {"reversed ewise mult does not match outer schemas? $a, $b"}
                    1 -> require( a.outer[0] == b.outer[0]) {"reversed matrix-vector element-wise multiply does not match shapes? $a, $b"}
                }
            }
        }

        override fun toString(): String {
            return "EMult${aligned.toCharStr()}($a, $b)"
        }

        companion object {
            fun estimateNnz(a: Construct, b: Construct): Nnz {
                val d = a.outerSchema
                val cz = listOf(a.nnz, b.nnz)
                val cd = listOf(a.outerSchema, b.outerSchema)
                return nnzInferer.inferMult(d, cz, cd)
            }
            // cost estimate is same as nnz estimate
            fun construct(buo: BottomUpOptimize, _a: Construct, _b: Construct, aligned: Boolean): EWiseMult {
                // compare by dim (matrices before vectors), then nnz (denser first), then id (smallest first)
                val (a, b) = orderAB(_a, _b)

                val nnz = estimateNnz(a, b)
                return EWiseMult(buo, a, b, nnz, nnz.toDouble(), aligned)
            }
        }

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (javaClass != other?.javaClass) return false

            other as EWiseMult

            if (a != other.a) return false
            if (b != other.b) return false
            if (aligned != other.aligned) return false

            return true
        }
        override fun hashCode(): Int {
            var result = a.hashCode()
            result = 31 * result + b.hashCode()
            result = 31 * result + aligned.hashCode()
            return result
        }

        override fun fillCMaps() {
            // over all pairs of a's cmap with b's cmaps, find those that match the construction here and add those in as new CMaps
            a.cmaps.filter { !it.complete }
                    .groupBy { it.tgtGraph }
                    .zipIntersect(b.cmaps.groupBy { it.tgtGraph }).forEach { tgi, (aml, bml) ->
                // Requirements: disjoint covered edges,
                // if both matrices or both vectors then same vertices; if matrix-vector then vector's vertex must be subet of matrix's vertices,
                // orientation matches EWiseMult alignment.
                // By construction, a has larger size. Candidate check is whether b's vertices are a subet of a's vertices.
                cmaps += aml.flatMap { am ->
                    bml.filter { bm ->
                        bm.vertMap.all { it in am.vertMap }
                                && (am.vertMap.last() == bm.vertMap.last()) == aligned
                                && am.coveredEdges.disjoint(bm.coveredEdges)
                    }.map { bm ->
                        // always take the vertMap of a.
                        CMap(this, tgi, am.vertMap, am.coveredEdges.or(bm.coveredEdges))
                    }
                }.toSet() // not pretty, but does the job
            }

        }

        override fun _convertToSNode(inputs: List<Pair<SNode, ABList>>): Pair<SNode, ABList> {
            // ensure that the inputs' attributes line up correctly.
            val (na, pa) = inputs[0]
            val (nb, pb) = inputs[1]
            when {
//                pa.isEmpty() -> return makeMultAbove(na, nb) to pb // not necessary; just second is okay because order
                pb.isEmpty() -> return makeMultAbove(na, nb) to pa
            }
            val ok = pb.all { it in pa } && (pa.last() == pb.last()) == aligned
            if (ok)
                return makeMultAbove(na, nb) to pa
            // rename second to match first
            val renameb = when (pa.size) {
                2 -> when (pb.size) {
                    2 -> if (aligned) mapOf(pb[0] to pa[0], pb[1] to pa[1]) else mapOf(pb[0] to pa[1], pb[1] to pa[0])
                    1 -> if (aligned) mapOf(pb[0] to pa[1]) else mapOf(pb[0] to pa[0])
                    else -> throw AssertionError()
                }
                1 -> mapOf(pb[0] to pa[0])
                else -> throw AssertionError()
            }
            val newb = makeRenameAbove(nb, renameb)
            return makeMultAbove(na, newb) to pa
        }
    }


    // used for vector-vector outer product and any-scalar multiply
    class Outer private constructor(
            buo: BottomUpOptimize, val a: Construct, val b: Construct, nnz: Nnz, thisCost: Double
    ) : Construct(buo, listOf(a,b), nnz, thisCost, a.outer + b.outer) {

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (javaClass != other?.javaClass) return false

            other as Outer

            if (a != other.a) return false
            if (b != other.b) return false

            return true
        }
        override fun hashCode(): Int {
            var result = a.hashCode()
            result = 31 * result + b.hashCode()
            return result
        }

        companion object {
            fun estimateNnz(a: Construct, b: Construct): Nnz {
                return a.nnz * b.nnz
            }
            fun construct(buo: BottomUpOptimize, _a: Construct, _b: Construct): Outer {
                // Choose the order of A and B such that the outer schema is constructed correctly, given the graph we target
//                val (a, b) = run {
//                    when {
//                        _a.outer.size != _b.outer.size -> if (_a.outer.size >= _b.outer.size) _a to _b else _b to _a
//                        // both vectors
//                        tgtA.outs == tgtMult.outs.subList(0, tgtA.outs.size) -> _a to _b
//                        else -> _b to _a
//                    }
//                }
                val (a, b) = orderAB(_a, _b)
                val nnz = estimateNnz(a, b)
                // Treat cost as 0 since we don't search over orders of vector and scalar multi
                return Outer(buo, a, b, nnz, 0.0)
            }

        }
        override fun fillCMaps() {
            // no CMaps for Outer; used as glue from tgts to tgtMult
        }

        override fun _convertToSNode(inputs: List<Pair<SNode, ABList>>): Pair<SNode, ABList> {
            return makeMultAbove(inputs[0].first, inputs[1].first) to inputs[0].second + inputs[1].second
        }
    }



    // Plus does not track CMaps or orientation.
    // This is okay for now because each graph is only represented in a single way during addition
    class Plus private constructor(
            buo: BottomUpOptimize, val a: Construct, val b: Construct, nnz: Nnz, thisCost: Double
    ) : Construct(buo, listOf(a, b), nnz, thisCost, a.outer) {

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (javaClass != other?.javaClass) return false

            other as Plus

            if (a != other.a) return false
            if (b != other.b) return false

            return true
        }
        override fun hashCode(): Int {
            var result = a.hashCode()
            result = 31 * result + b.hashCode()
            return result
        }

        companion object {
            fun estimateNnz(a: Construct, b: Construct): Nnz {
                val d = a.outerSchema
                val cz = listOf(a.nnz, b.nnz)
                val cd = listOf(a.outerSchema, b.outerSchema)
                return nnzInferer.inferAdd(d, cz, cd)
            }
            fun construct(buo: BottomUpOptimize, _a: Construct, _b: Construct): Plus {
                // compare by dim (matrices before vectors), then nnz (denser first), then id (smallest first)
                val (a, b) = orderAB(_a, _b)

                val nnz = estimateNnz(a, b)
                // Treat cost as 0 until we implement plus factorization or search over + orders
                return Plus(buo, a, b, nnz, 0.0)
            }

        }
        override fun fillCMaps() {
            // currently do not use CMaps for Plus
        }

        override fun _convertToSNode(inputs: List<Pair<SNode, ABList>>): Pair<SNode, ABList> {
            return makePlusAbove(inputs[0].first, inputs[1].first) to inputs[0].second + inputs[1].second
        }
    }


    class MatrixMult private constructor(
            buo: BottomUpOptimize, val a: Construct, val b: Construct, nnz: Nnz, thisCost: Double, outer: ShapeList, val type: MMType
    ) : Construct(buo, listOf(a, b), nnz, thisCost, outer) {

        enum class MMType(val aj: Int, val bj: Int) {
            MM00(0,0), MM01(0,1), MM10(1,0), MM11(1,1);

            companion object {
                fun fromInts(aj: Int, bj: Int): MMType = when (aj) {
                    0 -> when (bj) {
                        0 -> MM00
                        1 -> MM01
                        else -> throw IllegalArgumentException("$aj, $bj")
                    }
                    1 -> when (bj) {
                        0 -> MM10
                        1 -> MM11
                        else -> throw IllegalArgumentException("$aj, $bj")
                    }
                    else -> throw IllegalArgumentException("$aj, $bj")
                }
            }
        }

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (javaClass != other?.javaClass) return false

            other as MatrixMult

            if (a != other.a) return false
            if (b != other.b) return false
            if (type != other.type) return false

            return true
        }
        override fun hashCode(): Int {
            var result = a.hashCode()
            result = 31 * result + b.hashCode()
            result = 31 * result + type.hashCode()
            return result
        }

        override fun toString(): String = "$type($a, $b)"

        companion object {
            fun construct(buo: BottomUpOptimize, _a: Construct, _b: Construct, _aj: Int, _bj: Int): MatrixMult {
                val (a, b) = orderAB(_a, _b)
                val (aj, bj) = if (a === _a) _aj to _bj else _bj to _aj
                val ai = other01(aj)
                val bk = other01(bj)
                val outer = when {
                    b.outer.size == 2 -> listOf(a.outer[ai], b.outer[bk])
                    a.outer.size == 2 -> listOf(a.outer[ai])
                    else -> listOf()
                }
                val d = outer.toUnboundSchema()
                val cz = listOf(a.nnz, b.nnz)
                val cd = listOf(
                        if (outer.isNotEmpty()) mapOf<Name,Shape>(AU.U0 to a.outer[ai], AU.U2 to a.outer[aj]) else mapOf<Name,Shape>(AU.U2 to a.outer[aj]),
                        if (outer.size == 2) mapOf<Name,Shape>(AU.U2 to b.outer[bj], AU.U1 to b.outer[bk]) else mapOf<Name,Shape>(AU.U2 to b.outer[bj])
                )
                val nnz = nnzInferer.inferMatrixMult(d, cz, cd)

                // cost is 2*mult_nnz_estimate
                val multSchema = cd[0] + cd[1]
                val multNnz = nnzInferer.inferMult(multSchema, cz, cd)
                val cost = 2 * multNnz.toDouble()

                return MatrixMult(buo, a, b, nnz, cost, outer, MMType.fromInts(aj, bj))
            }
        }

        override fun fillCMaps() {
            // over all pairs of a's cmaps with b's cmaps, find those that match the construction here and add those in as new CMaps
            a.cmaps.filter { !it.complete }
                    .groupBy { it.tgtGraph }
                    .zipIntersect(b.cmaps.groupBy { it.tgtGraph }).forEach { tgi, (aml, bml) ->
                // Requirements: disjoint covered edges,
                // a and b match on a vertex in the correct position,
                // if b is a matrix then the other vertex in b does NOT match a's other vertex,
                // the matching vertex is not an output vertex in the target graph,
                // All incident edges on the matching vertex are covered in this construction.
                val tgts = buo.tgs.tgts[tgi]
                val tgtVertToAdjEdges = buo.tgs.tgtVertToAdjEdges[tgi]

                aml.flatMapTo(cmaps) { am ->
                    val aj = am.vertMap[type.aj]
                    if (aj in tgts.outs)
                        listOf()
                    else {
                        val ai = if (a.outer.size == 2 && b.outer.size == 2) am.vertMap[other01(type.aj)] else null

                        bml.filter { bm ->
                            aj == bm.vertMap[type.bj] // match on correct index
                                    && (ai == null || ai != bm.vertMap[other01(type.bj)]) // if matrix-matrix, the non-matching indices do not match
                                    && am.coveredEdges.disjoint(bm.coveredEdges) // child constructions have disjoint cmaps
                                    && tgtVertToAdjEdges[aj]!!.coveredBy(am.coveredEdges, bm.coveredEdges) // all incident edges covered
                        }.map { bm ->
                            val newVertMap = when {
                                b.outer.size == 2 -> listOf(ai!!, bm.vertMap[other01(type.bj)])
                                a.outer.size == 2 -> listOf(am.vertMap[other01(type.aj)])
                                else -> listOf()
                            }
                            CMap(this, tgi, newVertMap, am.coveredEdges.or(bm.coveredEdges))
                        }
                    }
                }
            }
        }

        override fun _convertToSNode(inputs: List<Pair<SNode, ABList>>): Pair<SNode, ABList> {
            val (na, pa) = inputs[0]
            val (nb, pb) = inputs[1]

            val aj = type.aj; val bj = type.bj
            // rename pb: position bj to aj; ensure distinct bk from ak

            val (newb, mxmSchema) = if (pa.size == 2 && pb.size == 2) {
                val ai = other01(aj)
                val bk = other01(bj)
                val mapping =
                        (if (pa[aj] != pb[bj]) mapOf(pb[bj] to pa[aj]) else mapOf()) +
                                (if (pa[ai] == pb[bk] || pb[bk] == pa[aj]) mapOf(pb[bk] to pb[bk].deriveFresh()) else mapOf())
                val newb = if (mapping.isEmpty()) nb else makeRenameAbove(nb, mapping)
                val mxmSchema = listOf(pa[ai], mapping.getOrElse(pb[bk]) {pb[bk]})
                newb to mxmSchema
            } else {
                val newb = if (pa[aj] == pb[bj]) nb else makeRenameAbove(nb, mapOf(pb[aj] to pa[aj]))
                val mxmSchema = if (pa.size == 2) listOf(pa[other01(aj)]) else listOf()
                newb to mxmSchema
            }

            return makeAggAbove(makeMultAbove(na, newb), pa[aj]) to mxmSchema
        }
    }


    class Agg private constructor(
            buo: BottomUpOptimize, val a: Construct, nnz: Nnz, thisCost: Double, val aggPos: Int
    ) : Construct(buo, listOf(a), nnz, thisCost, a.outer.allBut(aggPos)) {

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (javaClass != other?.javaClass) return false

            other as Agg

            if (a != other.a) return false
            if (aggPos != other.aggPos) return false

            return true
        }
        override fun hashCode(): Int {
            var result = a.hashCode()
            result = 31 * result + aggPos
            return result
        }

        companion object {
            fun construct(buo: BottomUpOptimize, a: Construct, aggPos: Int): Agg {
                val cz = a.nnz
                val cd = a.outerSchema
                val d = a.outerSchema - AU(aggPos)
                val nnz = nnzInferer.inferAgg(d, cz, cd)

                // cost is 0 if child is also an Agg, becaue the Aggs can be combined.
                val cost = if (a is Agg) 0.0 else a.nnz.toDouble()
                return Agg(buo, a, nnz, cost, aggPos)
            }
        }

        override fun fillCMaps() {
            // Requirements: aggregated vertex is "full":
            //      there do not exist uncovered edges incident on the outer schema
            a.cmaps.filter { !it.complete }
                    .groupBy { it.tgtGraph }
                    .forEach { tgi, aml ->
                val tg = buo.tgs.tgts[tgi]
                val tgtEdges = buo.tgs.tgtEdgeListNoScalars[tgi]

                aml.mapNotNullTo(cmaps) { am ->
                    val aggVert = am.vertMap[aggPos]
                    if (aggVert in tg.aggs && am.coveredEdges.withIndex().all { (ei, b) ->
                        b || aggVert !in tgtEdges[ei].verts
                    })
                        CMap(this, am.tgtGraph, am.vertMap.allBut(aggPos), am.coveredEdges)
                    else null
                }
            }
        }

        override fun _convertToSNode(inputs: List<Pair<SNode, ABList>>): Pair<SNode, ABList> {
            val (n, p) = inputs[0]
            return makeAggAbove(n, p[aggPos]) to (p - p[aggPos])
        }
    }


//    class Transpose(val a: Construct): Construct(listOf(a), a.nnz, 0.0, a.outer.reversed()) {
//        init {
//            require(a.outer.size == 2)
//        }
//
//        override fun fillCMaps() {
//            // no CMaps; special use
//        }
//
//        override fun _convertToSNode(inputs: List<SNode>, memoAttrPosList: MutableMap<Id, ABList>): SNode {
//            val n = inputs[0]
//            assert(n.schema.size == 2)
////            if (n.schema.size < 2)
////                return n
////            val p = SHash.createAttributePositionList(n, memoAttrPosList)
////            if (p == expectedOuts.map(ABS::a))
////                return n
//
//            @Suppress("UNCHECKED_CAST")
//            val rename = n.schema.keys.toList().let { it as ABList; it.zip(it.reversed()).toMap() }
//            return makeRenameAbove(n, rename)
//        }
//
//        override fun equals(other: Any?): Boolean {
//            if (this === other) return true
//            if (javaClass != other?.javaClass) return false
//
//            other as Transpose
//
//            if (a != other.a) return false
////            if (expectedOuts != other.expectedOuts) return false
//
//            return true
//        }
//        override fun hashCode(): Int {
//            var result = a.hashCode()
////            result = 31 * result + expectedOuts.hashCode()
//            return result
//        }
//    }

    class Rename(buo: BottomUpOptimize, val a: Construct, val schema: ABList): Construct(buo, listOf(a), a.nnz, 0.0, a.outer) {
        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (javaClass != other?.javaClass) return false

            other as Rename

            if (a != other.a) return false
            if (schema != other.schema) return false

            return true
        }
        override fun hashCode(): Int {
            var result = a.hashCode()
            result = 31 * result + schema.hashCode()
            return result
        }

        override fun fillCMaps() {}

        override fun _convertToSNode(inputs: List<Pair<SNode, ABList>>): Pair<SNode, ABList> {
            val (n, p) = inputs[0]
            val mapping = p.zip(schema).toMap()
            return makeRenameAbove(n, mapping) to schema
        }
    }

}


private fun <E> List<E>.allBut(pos: Int): List<E> {
    require(pos in indices)
    return when {
        size == 1 -> listOf()
        pos == size-1 -> subList(0, size-1)
        pos == 0 -> subList(1, size)
        else -> subList(0, pos) + subList(pos + 1, size)
    }
}

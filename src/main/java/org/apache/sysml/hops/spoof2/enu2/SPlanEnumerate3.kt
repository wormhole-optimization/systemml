package org.apache.sysml.hops.spoof2.enu2

import org.apache.commons.logging.LogFactory
import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.LiteralOp
import org.apache.sysml.hops.spoof2.*
import org.apache.sysml.hops.spoof2.enu.ENode
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.RewriteBindElim.Companion.eliminateNode
import java.util.*
import kotlin.NoSuchElementException

// optional SNode
sealed class SNodeOption {
    abstract fun toNode(): SNode?
    data class Some(val node: SNode): SNodeOption() { // consider parameterizing <N:SNode>
        override fun toNode() = node
    }
    object None : SNodeOption() {
        override fun toNode() = null
    }
//    inline fun tryApply(f: (SNode) -> Unit) = when (this) {
//        None -> {}
//        is Some -> f(this.node)
//    }
    inline fun <R:Any> tryApply(f: (SNode) -> R): R? = when (this) {
        None -> null
        is Some -> f(this.node)
    }
    inline fun map(f: (SNode) -> SNode): SNodeOption = when (this) {
        None -> None
        is Some -> Some(f(node))
    }
}
private fun SNode.toOption() = SNodeOption.Some(this)

typealias Monomorph = Map<ABS,ABS>
typealias GraphBag = List<Graph>
fun GraphBag.isCanonical() = this.all(Graph::isCanonical)
fun GraphBag.outs() = this.flatMap(Graph::outs).toSet()
fun GraphBag.rename(h: Monomorph): GraphBag = this.map { it.rename(h) }
fun GraphBag.toSNode(): SNode {
    if (this.size == 1)
        return this[0].toSNode()
    return SNodeNary(SNodeNary.NaryOp.PLUS, this.map { it.toSNode() })
}
fun Schema.toABS() = this.map { (a,s) -> ABS(a as AB,s) }.toSet()
/** Does this list not contain a duplicate (according to equals())? */
fun <T> List<T>.noDups() = this.size == this.toSet().size

data class AttributeBoundShape(val a: AB, val s: Shape) {
//    fun rename(aNew: AB) = AttributeBoundShape(aNew, s)
}
typealias ABS = AttributeBoundShape

sealed class Edge(open val base: Any, val verts: List<ABS>) {
    abstract fun isCanonical(): Boolean
    abstract fun rename(h: Monomorph): Edge
    abstract fun toSNode(): SNode

    class C(override val base: SNode, verts: List<ABS>): Edge(base, verts) {
        override fun isCanonical() = true
        override fun rename(h: Monomorph) = C(base, verts.map { h[it] ?: it })
        override fun toSNode(): SNode {
            if (verts.isEmpty())
                return base
            val bindings = verts.mapIndexed { i, v -> AU(i) to v.a }.toMap()
            return SNodeBind(base, bindings)
        }
    }
    class F(override val base: GraphBag, outs: List<ABS>): Edge(base, outs) {
        init { require(outs.toSet() == base.outs()) }
        override fun isCanonical() = false
        override fun rename(h: Monomorph) = F(base.rename(h), verts.map { h[it] ?: it })
        override fun toSNode(): SNode = base.toSNode()
        // Careful with equals() and hashCode() on Edge.F
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as Edge

        if (base != other.base) return false
        if (verts != other.verts) return false

        return true
    }
    override fun hashCode(): Int {
        var result = base.hashCode()
        result = 31 * result + verts.hashCode()
        return result
    }
}

data class Graph(val outs: Set<ABS>, val edges: List<Edge>) {
    val verts = edges.flatMap { it.verts }.toSet()
    val aggs: Set<ABS> = verts - outs
    //    val outAtts = outs.map(ABS::a)
//    val aggAtts = aggs.map(ABS::a)
//    val vertAtts = verts.map(ABS::a)
    init {
//        val outAtts = outs.map(ABS::a)
//        val aggAtts = aggs.map(ABS::a)
//        require((outAtts + aggAtts).noDups()) {"overlap between outs and aggs: $outs, $aggs"}
        require(verts.map(ABS::a).noDups()) {"a name appears twice in a graph with different shapes; $this"}
//        require(verts == edges.flatMap(Edge::verts).toSet()) {"vertices disagree with edges: $verts, $edges"}
    }
    fun isCanonical() = edges.all(Edge::isCanonical)
    fun rename(h: Monomorph) = Graph(outs.map { h[it] ?: it }.toSet(), edges.map { it.rename(h) })
    fun toSNode(): SNode {
        if (edges.isEmpty()) return SNodeData(LiteralOp(1.0))
        val mult = if (edges.size == 1) edges[0].toSNode()
        else SNodeNary(SNodeNary.NaryOp.MULT, edges.map { it.toSNode() })
        val agg = if (aggs.isEmpty()) mult
        else SNodeAggregate(Hop.AggOp.SUM, mult, aggs.map(ABS::a))
        return agg
    }
    fun edgeGroups(): List<Set<ABS>> {
        return edges.map { it.verts.toSet() }.distinct()
    }
    fun buildOneHopMap(vertSubset: Set<ABS> = verts): Map<ABS, Set<ABS>> {
        val tmp = mutableMapOf<ABS, MutableSet<ABS>>()
        edges.forEach {
            // v to neighbors of v
            for (i in it.verts.indices)
                for (j in i+1 until it.verts.size)
                    tmp.getOrPut(it.verts[i], ::mutableSetOf) += it.verts[j]
        }
        return tmp
    }
}

//data class GraphBag(val graphs: List<Graph>) {
//    fun isCanonical() = graphs.all(Graph::isCanonical)
//}

private fun checkPlusFactorization(Gf: Graph, h: Monomorph, G: Graph) {
    check(h.keys.map(ABS::a).noDups()) {"h is a relation, not a function; duplicate name in keys of $h"}
    check(h.values.map(ABS::a).noDups()) {"h is not 1-1; duplicate name in values of $h"}
//    check(h.values.size == h.values.toSet().size) {"h is not 1-1: $h"}
    for (v in Gf.verts) {
        check(v in h) {"h is a partial function; undefined on input $v: $h"}
        val vp = h[v]!!
        check(v.s == vp.s) {"h maps an index to a different shape: $v to $vp"}
        check(vp in G.verts) {"h maps $v to $vp which is not in G: $G"}
        if (v in Gf.outs)
            check(vp == v) {"non-stationary output under h: $v maps to $vp"}
        else
            check(G.verts.none { it.a == v.a }) {"non-fresh agg. index $v; overlaps with graph $G"}
    }
    for (e in Gf.edges) {
        check(e.rename(h) in G.edges) {"an edge in Gf does not map to an edge in G under h: $e is not in $G"}
    }
}

data class CanonMemo(
        val ctb: MutableMap<GraphBag, GraphBagCanon> = mutableMapOf(),
        val ctg: MutableMap<Graph, GraphCanon> = mutableMapOf(),
        val ntb: MutableMap<Hash, Pair<GraphBagCanon, SNodeOption>> = mutableMapOf(),
        val ntg: MutableMap<Hash, Pair<GraphCanon, SNodeOption>> = mutableMapOf()
) {
    val literalOne by lazy { SNodeData(LiteralOp(1.0)) }
//    operator fun get(B: GraphBag): GraphBagCanon = canonize(B)
//    operator fun get(G: Graph): GraphCanon = canonize(G)
//    operator fun get(E: Edge.F): Hash = /*htEF[E] ?:*/ GraphCanonizer.hash(E, this)
//    operator fun set(B: GraphBag, h: Hash) = ctb.set(B, h)
//    operator fun set(G: Graph, h: GraphCanon) = ctg.set(G, h)
//    operator fun set(E: Edge.F, h: Hash) = htEF.set(E, h)
//    operator fun contains(B: GraphBag) = B in ctb
//    operator fun contains(G: Graph) = G in ctg
//    operator fun contains(E: Edge.F) = E in htEF
    private inline fun getOrPut(b: GraphBag, f: (GraphBag) -> GraphBagCanon): GraphBagCanon = if (b in ctb) ctb[b]!! else f(b).also { ctb[b] = it }
    private inline fun getOrPut(b: Graph, f: (Graph) -> GraphCanon): GraphCanon = if (b in ctg) ctg[b]!! else f(b).also { ctg[b] = it }
//    inline fun getOrPut(b: Edge.F, f: (Edge.F) -> Hash): Hash = if (b in htEF) htEF[b]!! else f(b).also { htEF[b] = it }

    fun canonize(b: GraphBag): GraphBagCanon = this.getOrPut(b) {
        val beforeSort = b.map { canonize(it) }//.sorted().joinToString("~")
        val perm = SHash.sortIndicesHierarchical(beforeSort, listOf<(GraphCanon) -> Hash>({ it.hash }))
        val hash = beforeSort.permute(perm).joinToString("~")
        GraphBagCanon(b, beforeSort, perm, hash)
    }
    fun canonize(g: Graph): GraphCanon = this.getOrPut(g) {
        val gc = GraphCanonizer(g, this)
        gc.canonize()
    }
    fun canonize(e: Edge): Hash = when (e) {
        is Edge.C -> canonize(e)
        is Edge.F -> canonize(e)
    }
    fun canonize(e: Edge.C): Hash = e.base.id.toString()
    fun canonize(e: Edge.F): Hash = canonize(e.base).hash

    /** If [b] was previously explored and a node was memoized representing its alternatives,
     * then adapt the node to the output indices of [b] and return it.
     * Returns an [SNodeOption] if it is in the memo (whose node is adapted if the option is Some).
     * Returns null if the canonical form of [b] is not in the memo. */
    fun adaptFromMemo(b: GraphBag): SNodeOption? {
        val bc = canonize(b)
        return ntb[bc.hash]?.let { (sc, no) ->
            no.map { adaptFromMemo(bc, sc, it) }
        }
    }
    /** If [g] was previously explored and a node was memoized representing its alternatives,
     * then adapt the node to the output indices of [g] and return it. */
    fun adaptFromMemo(g: Graph): SNodeOption? {
        val gc = canonize(g)
        return ntg[gc.hash]?.let { (sc, no) ->
            when (no) {
                SNodeOption.None -> no
                is SNodeOption.Some -> no.map { adaptFromMemo(gc, sc, it) }
            }
        }
    }

    fun memoize(b: GraphBag, n: SNodeOption) {
        val bc = canonize(b)
        ntb[bc.hash] = bc to n
    }
    fun memoize(g: Graph, n: SNodeOption) {
        val gc = canonize(g)
        ntg[gc.hash] = gc to n
    }

    private fun findPairIndex(newOut: ABS, gc: GraphCanon, sc: GraphCanon): ABS {
        val gcVertIdx = gc.verts.indexOf(newOut)
        val gcPos = gc.perm[gcVertIdx]
        val scVertIdx = sc.perm.indexOf(gcPos)
        val oldOut = sc.verts[scVertIdx]
        return oldOut
    }

    /** Adapt node [n] created with [sc] to the isomorphic new canon [gc]. */
    private fun adaptFromMemo(gc: GraphCanon, sc: GraphCanon, n: SNode): SNode {
        if (gc.orig.outs == n.schema.toABS()) return n
        val new2old = gc.orig.outs.map { it to findPairIndex(it, gc, sc) }
        val i2old = new2old.mapIndexed { i, (_,o) -> AU(i) to o.a}.toMap()
        val i2new = new2old.mapIndexed { i, (n,_) -> AU(i) to n.a}.toMap()
        val u = SNodeUnbind(n, i2old)
        val b = SNodeBind(u, i2new)
        return b
    }
    /** Adapt node [n] created with [sc] to the isomorphic new canon [bc]. */
    private fun adaptFromMemo(bc: GraphBagCanon, sc: GraphBagCanon, n: SNode): SNode {
        if (bc.orig.outs() == n.schema.toABS()) return n
        // get aligned GraphCanons to pair output indices
        val outsRemain = ArrayList(bc.orig.outs())
        val new2old: MutableList<Pair<ABS, ABS>> = mutableListOf()
        loop@ while (outsRemain.isNotEmpty()) {
            val newOut = outsRemain.removeAt(outsRemain.size-1)
            for (i in bc.orig.indices) {
                val bcg = bc.orig[bc.perm.indexOf(i)]
                if (newOut !in bcg.outs) continue
                val scg = sc.orig[sc.perm.indexOf(i)]
                val bcgc = canonize(bcg)
                val scgc = canonize(scg)
                new2old += newOut to findPairIndex(newOut, bcgc, scgc)
                continue@loop
            }
            throw AssertionError("unreachable")
        }
        val i2old = new2old.mapIndexed { i, (_,o) -> AU(i) to o.a}.toMap()
        val i2new = new2old.mapIndexed { i, (n,_) -> AU(i) to n.a}.toMap()
        val u = SNodeUnbind(n, i2old)
        val b = SNodeBind(u, i2new)
        return b
    }
}



class SPlanEnumerate3(initialRoots: Collection<SNode>) {
    constructor(vararg inputs: SNode) : this(inputs.asList())
    private val LOG = LogFactory.getLog(SPlanEnumerate3::class.java)!!
    companion object {
        // todo - configuration parameters for whether to expand +, prune, etc.
        private const val SOUND_PRUNE_TENSOR_INTERMEDIATE = true
        private const val UNSOUND_PRUNE_MAX_DEGREE = true
    }

    private val remainingToExpand = HashSet(initialRoots)
    //    private val seen = HashSet<Id>()
//    private val ht: BiMap<Hash, SNode> = HashBiMap.create()
    private val memo: CanonMemo = CanonMemo()
    private val planCost = PlanCost()



    fun expandAll() {
        while( remainingToExpand.isNotEmpty() )
            expand()
    }

    private fun expand() {
        expand(remainingToExpand.removeFirst() ?: return)
    }

    private fun expand(node: SNode) {
//        if( node in ht.values ) // todo replace with visit flag
//            return

        when( node ) {
            is SNodeData -> return node.inputs.forEach { expand(it) }
            is SNodeExt -> return node.inputs.forEach { expand(it) }
            is SNodeUnbind -> return expand(node.input)
            is SNodeBind -> return expand(node.input)
            is OrNode -> return // OrNodes are already expanded.
            is ENode -> throw AssertionError("unexpected ENode")
            is SNodeAggregate -> if (node.op != Hop.AggOp.SUM ) return expand(node.input)
            is SNodeNary -> if (node.op != SNodeNary.NaryOp.MULT && node.op != SNodeNary.NaryOp.PLUS) return node.inputs.forEach { expand(it) }
        }
        // check ht here?

        // strip away parents, add parents to result, in same input location
        val pa: List<SNode> = ArrayList(node.parents)
        val paIdx = pa.map {
            val idx = it.inputs.indexOf(node)
            it.inputs.removeAt(idx)
            idx
        }
        node.parents.clear()

        val b: GraphBag = toGraphBag(node)
        val r = factorPlus(b)
        node.check(r is SNodeOption.Some) {"no expansion possible"}
        val rn = (r as SNodeOption.Some).node

        pa.zip(paIdx).forEach { (p, i) ->
            p.inputs.add(i, rn)
            rn.parents.add(p)
        }
    }

    // normal form to graph bag
    private fun toGraphBag(node: SNode): GraphBag {
        return if (node is SNodeNary && node.op == SNodeNary.NaryOp.PLUS) {
            node.inputs.map { it.parents -= node; toGraph(it) }
        } else listOf(toGraph(node))
    }

    private fun toGraph(node: SNode): Graph {
        val (aggs0, mult) = if (node is SNodeAggregate && node.op == Hop.AggOp.SUM) {
            node.input.parents -= node
            node.aggs to node.input
        } else Schema() to node
        val bases = if (mult is SNodeNary && mult.op == SNodeNary.NaryOp.MULT) {
            mult.inputs.forEach { it.parents -= mult }
            mult.inputs
        } else listOf(mult)
        val aggs = aggs0.toABS()
        val edges = bases.map { toEdge(it) }
        val outs = edges.flatMap { it.verts }.toSet() - aggs //bases.flatMap { it.schema.toABS() }.toSet() - aggs
        return Graph(outs, edges)
    }

    private fun toEdge(node: SNode): Edge.C {
        val base = getBase(node)
        val attrPosList = SHash.createAttributePositionList(node) // todo: cache memo
        val verts = attrPosList.map { ABS(it, base.schema[it]!!) }
        return Edge.C(base, verts)
    }

    private fun getBase(node0: SNode): SNode {
        var node = node0
        while (node is SNodeBind || node is SNodeUnbind) {
            node.inputs[0].parents -= node
            node = node.inputs[0]
        }
        return node
    }

    private fun factorPlus(b: GraphBag): SNodeOption {
        if (b.size == 1)
            return factorAgg(b[0])
        // compute canonical form, check if canonical form has an SNode, if so adapt the SNode to this one
        memo.adaptFromMemo(b)?.let { return it }
        val r = factorPlusRec(listOf(), b, listOf(), 0, 1)
        memo.memoize(b, r)
        return r
    }

    private fun factorPlusRec(Bold: GraphBag, Bcur: GraphBag, Bnew: GraphBag, i0: Int, j0: Int): SNodeOption {
        if (Bcur.isEmpty() && Bnew.isEmpty()) return factorPlusBase(Bold)
        val (i, j) = if (j0 > Bold.size + Bcur.size) i0+1 to i0+2 else i0 to j0
        if (i > Bcur.size) return factorPlusRec(Bold + Bcur, Bnew, listOf(), 0, 1)
        val alts = mutableListOf<SNode>()
        // 1. Explore not factoring common terms
        factorPlusRec(Bold, Bcur, Bnew, i, j+1).tryApply { alts += it }
        // 2. Explore factoring out
        val Gi = Bcur[i]
        val Gj = if (j < Bcur.size) Bcur[j] else Bold[j-Bcur.size]
        for ((Gf: Graph, hi: Monomorph, hj: Monomorph) in enumFactorization(Gi, Gj)) {
            checkPlusFactorization(Gf, hi, Gi)
            checkPlusFactorization(Gf, hj, Gj)
            val Bp = mutableListOf<Graph>()
            // if factoring out results in a single edge and it is a factored graphbag, then add all its graphs to Bp
            // otherwise add the graph resulting from factoring out
            Bp += factorOutTerms(Gf, hi, Gi) // lines 11 to 19
            Bp += factorOutTerms(Gf, hj, Gj)

            val Op = Bp.outs()
            if (SOUND_PRUNE_TENSOR_INTERMEDIATE && Op.size > 2) continue

            // put output vertices in order of canonical graph order
            val BpSortedC = memo.canonize(Bp).orderCanon()
            val BpEdge = Edge.F(BpSortedC.orig, BpSortedC.orderOuts())
            // todo - make sure this BpEdge is compatible with enumFactorization so that it can be factored out later
            assert(Gf.outs+Op == Gi.outs+Gj.outs)
            val Gp = Graph(Gf.outs + Op, Gf.edges + BpEdge)

            val newBold: GraphBag; val newBcur: GraphBag
            if (j < Bcur.size) { newBold = Bold; newBcur = Bcur - Gi - Gj }
            else { newBold = Bold - Gj; newBcur = Bcur - Gi }
            factorPlusRec(newBold, newBcur, Bnew + Gp, i, i+1).tryApply { alts += it }
        }
        return optionOrNode(alts)
    }

    private fun factorOutTerms(Gf: Graph, h: Monomorph, G: Graph): List<Graph> {
        val Ep = G.rename(h).edges - Gf.edges
        if (Ep.size == 1 && Ep[0] is Edge.F) {
            return (Ep[0] as Edge.F).base
        }
        val Vp = Ep.flatMap { it.verts }.toSet()
        val outs = Vp.intersect(Gf.verts + G.outs)
        val aggs = G.aggs - h.values
        val Gp = Graph(outs, Ep)
        assert(aggs == Gp.aggs)
        return listOf(Gp)
    }

    private fun factorPlusBase(B: GraphBag): SNodeOption {
        if (B.size == 1) return factorAgg(B[0])
        memo.adaptFromMemo(B)?.let { return it }
        val alts: MutableList<SNode> = mutableListOf()
        for ((B1, B2) in enumPartition(B)) {
            val r1 = factorPlusBase(B1).toNode() ?: continue
            val r2 = factorPlusBase(B2).toNode() ?: continue
            alts += SNodeNary(SNodeNary.NaryOp.PLUS, r1, r2)
        }
        val r = optionOrNode(alts)
        memo.memoize(B, r)
        return r
    }

    // further optimization - detect when some elements in list are equal; don't enumerate the same state more than once
    private fun <T> enumPartition(l: List<T>): Sequence<Pair<List<T>,List<T>>> {
        return object : Sequence<Pair<List<T>,List<T>>> {
            override fun iterator(): Iterator<Pair<List<T>, List<T>>> {
                return EnumPartition(l)
            }
        }
    }

    class EnumPartition<T>(val l: List<T>) : Iterator<Pair<List<T>, List<T>>> {
        private val asn = BooleanArray(l.size) // true means in first partition
        private var sz1 = 1
        init { asn[0] = true }

        override fun hasNext(): Boolean {
            return sz1 <= (l.size/2)
        }

        override fun next(): Pair<List<T>, List<T>> {
            if (!hasNext()) throw NoSuchElementException()
            val r = l.partitionIndexed { (i,_) -> asn[i] }

            // update state to next
            var c = 0 // count of trues at end
            while (asn[asn.size - c - 1]) {
                asn[asn.size - c - 1] = false
                c++
            }
            if (c == sz1) { // last for size
//                    asn.fill(false, asn.size-sz1, asn.size)
                sz1++
                if (sz1 <= l.size / 2)
                    asn.fill(true, 0, sz1)
            } else {
                // delete next true and add c+1 trues after it
                var firstTrue = asn.size - c - 2
                while (!asn[firstTrue]) firstTrue--
                asn[firstTrue] = false
                asn.fill(true, firstTrue + 1, firstTrue + 1 + c + 1)
                if (l.size % 2 == 0 && sz1 == l.size/2 && firstTrue == 0)
                    sz1++
            }
            return r
        }

//        private fun lastForSize(): Boolean {
//            for (i in asn.size-sz1 until asn.size)
//                if (!asn[i]) return false
//            return true
//        }
    }

    private fun factorAgg(g: Graph): SNodeOption {
        if (g.aggs.isEmpty()) return factorMult(g.edges, true)
        memo.adaptFromMemo(g)?.let { return it }
        val partitions: List<Graph> = partitionByAggCC(g)
        if (partitions.size > 1) {
            val ep = partitions.map { p ->
                val l = factorAgg(p)
                val gc = memo.canonize(p)
                Edge.F(listOf(p), gc.orderVertsCanon(p.outs))
            }
            val r = factorMult(ep, false)
            memo.memoize(g, r)
            return r
        }
        if (SOUND_PRUNE_TENSOR_INTERMEDIATE && g.outs.size > 2) return SNodeOption.None
        if (g.aggs.size == 1 || g.edgeGroups().size == 1) {
            val mult = factorMult(g.edges, true).toNode() ?: return SNodeOption.None
            val agg = SNodeAggregate(Hop.AggOp.SUM, mult, g.aggs.map(ABS::a))
            val r = agg.toOption()
            memo.memoize(g, r)
            return r
        }
        val aggsEnu = if (UNSOUND_PRUNE_MAX_DEGREE) {
            val dmap: Map<ABS, Int> = memo.canonize(g).v2ns.mapValues { (_,v) -> v.size }
            val dmax = dmap.values.max()!!
            g.aggs.filter { dmap[it] == dmax }.toSet()
        } else g.aggs
        val alts: MutableList<SNode> = mutableListOf()
        for (v in aggsEnu) {
            val gbelow = Graph(g.outs + v, g.edges)
            val below = factorAgg(gbelow)
            below.tryApply { alts += it }
        }
        val r = optionOrNode(alts)
        memo.memoize(g, r)
        return r
    }

    private fun partitionByAggCC(g: Graph): List<Graph> {
        val aggOneHop = g.buildOneHopMap(g.aggs)
        val aggCCs = findCCs(aggOneHop)
        return aggCCs.map { aggCC ->
            val ei = g.edges.filter { !it.verts.disjoint(aggCC) }
            val oi = g.outs.intersect(ei.flatMap { it.verts })
            Graph(oi, ei)
        } + run {
            val e0 = g.edges.filter { it.verts.disjoint(g.aggs) }
            val o0 = e0.flatMap { it.verts }.toSet()
            Graph(o0, e0)
        }
    }

    private fun factorMult(es: List<Edge>, useMemo: Boolean): SNodeOption {
        // TODO - memo for edges - not as complicated as Graphs
        //if (useMemo) memo.adaptFromMemo(es)?.let { return it }
        if (es.isEmpty()) return memo.literalOne.toOption()
        if (es.size == 1) {
            val e = es[0]
            return when (e) {
                is Edge.C -> e.base.toOption()
                is Edge.F -> factorPlusBase(e.base)
            }
        }
        val alts: MutableList<SNode> = mutableListOf()
        for ((es1, es2) in enumPartition(es)) {
            val r1 = factorMult(es1, true).toNode() ?: continue
            val r2 = factorMult(es2, true).toNode() ?: continue
            alts += SNodeNary(SNodeNary.NaryOp.MULT, r1, r2)
        }
        val r = optionOrNode(alts)
//        if (useMemo) memo.memoize(es, r)
        return r
    }

    private fun optionOrNode(alts: List<SNode>): SNodeOption = when(alts.size) {
        0 -> SNodeOption.None
        1 -> alts[0].toOption()
        else -> OrNode(alts).toOption()
    }

}
package org.apache.sysml.hops.spoof2.enu2

import org.apache.commons.logging.LogFactory
import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.LiteralOp
import org.apache.sysml.hops.spoof2.*
import org.apache.sysml.hops.spoof2.enu.ENode
import org.apache.sysml.hops.spoof2.enu2.PrefixRejectTopIter.PrefixRejectZone
import org.apache.sysml.hops.spoof2.enu2.PrefixRejectTopIter.PrefixRejectZone.Companion.orderGenPrz
import org.apache.sysml.hops.spoof2.plan.*
import java.util.*

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
    return makePlusAbove(this.map { it.toSNode() })
}
fun Schema.toABS() = this.map { (a,s) ->
    ABS(a as AB,s)
}.toSet()
/** Does this list not contain a duplicate (according to equals())? */
fun <T> List<T>.noDups() = this.size == this.toSet().size

data class AttributeBoundShape(val a: AB, val s: Shape) {
    //    fun rename(aNew: AB) = AttributeBoundShape(aNew, s)
    override fun toString() = "\$$a"
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
            return makeBindAbove(base, bindings)
        }
        override fun toString() = "Edge.C<${verts.joinToString(",")}>(${base.id}@${
            when(base) {
                is org.apache.sysml.hops.spoof2.plan.SNodeData -> base.hop.opString
                else -> base.toString()
            }
        })"
    }
    class F(override val base: GraphBag, outs: List<ABS>): Edge(base, outs) {
        init { require(outs.toSet() == base.outs()) }
        override fun isCanonical() = false
        override fun rename(h: Monomorph) = F(base.rename(h), verts.map { h[it] ?: it })
        override fun toSNode(): SNode = base.toSNode()
        // Careful with equals() and hashCode() on Edge.F
        override fun toString() = "Edge.F<${verts.joinToString(",")}>{{$base}}"
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
        else makeMultAbove(edges.map { it.toSNode() })
        val agg = if (aggs.isEmpty()) mult
        else makeAggAbove(mult, aggs.map(ABS::a).toSet())
        return agg
    }
    fun edgeGroups(): List<Set<ABS>> {
        return edges.map { it.verts.toSet() }.distinct()
    }
    fun buildOneHopMapUndirected(vertSubset: Set<ABS> = verts): Map<ABS, Set<ABS>> {
        val tmp = mutableMapOf<ABS, MutableSet<ABS>>()
        edges.forEach {
            // v to neighbors of v
            for ((i,vi) in it.verts.withIndex()) {
                if (vi !in vertSubset) continue
                for (j in i + 1 until it.verts.size) {
                    val vj = it.verts[j]
                    if (vj !in vertSubset) continue
                    tmp.getOrPut(vi, ::mutableSetOf) += vj
                    tmp.getOrPut(vj, ::mutableSetOf) += vi
                }
            }
        }
        return tmp
    }
    override fun toString() = "Graph<${outs.joinToString(",")}>$edges"
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
        val ntb: MutableMap<Rep, Pair<GraphBagCanon, SNodeOption>> = mutableMapOf(),
        val ntg: MutableMap<Rep, Pair<GraphCanon, SNodeOption>> = mutableMapOf()
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

    // A GraphBag of size 1 has the same rep as its sigle Graph.
    fun canonize(b: GraphBag): GraphBagCanon = this.getOrPut(b) {
        val beforeSort = b.map { canonize(it) }//.sorted().joinToString("~")
        val perm = SHash.sortIndicesHierarchical(beforeSort, listOf<(GraphCanon) -> Rep>({ it.rep }))
        val rep: Rep = beforeSort.permute(perm).joinToString("~")
        GraphBagCanon(b, beforeSort, perm, rep)
    }
    fun canonize(g: Graph): GraphCanon = this.getOrPut(g) {
        val gc = GraphCanonizer(g, this)
        gc.canonize()
    }
    fun canonize(e: Edge): Rep = when (e) {
        is Edge.C -> canonize(e)
        is Edge.F -> canonize(e)
    }
    fun canonize(e: Edge.C): Rep = e.base.id.toString()
    fun canonize(e: Edge.F): Rep = canonize(e.base).rep

    /** If [b] was previously explored and a node was memoized representing its alternatives,
     * then adapt the node to the output indices of [b] and return it.
     * Returns an [SNodeOption] if it is in the memo (whose node is adapted if the option is Some).
     * Returns null if the canonical form of [b] is not in the memo. */
    fun adaptFromMemo(b: GraphBag): SNodeOption? {
        val bc = canonize(b)
        return ntb[bc.rep]?.let { (sc, no) ->
            no.map {
//                if (it !in it.inputs[0].parents) { // restore parents
//                    it.inputs.forEach { inp -> inp.parents += it }
//                }
                adaptFromMemo(bc, sc, it)
            }
        }
    }
    /** If [g] was previously explored and a node was memoized representing its alternatives,
     * then adapt the node to the output indices of [g] and return it. */
    fun adaptFromMemo(g: Graph): SNodeOption? {
        val gc = canonize(g)
        return ntg[gc.rep]?.let { (sc, no) ->
            no.map {
//                if (it !in it.inputs[0].parents) { // restore parents
//                    it.inputs.forEach { inp -> inp.parents += it }
//                }
                adaptFromMemo(gc, sc, it)
            }
        }
    }

    fun memoize(b: GraphBag, n: SNodeOption) {
        val bc = canonize(b)
        ntb[bc.rep] = bc to n
    }
    fun memoize(g: Graph, n: SNodeOption) {
        val gc = canonize(g)
        ntg[gc.rep] = gc to n
    }

    private fun findPairIndex(newOut: ABS, gc: GraphCanon, sc: GraphCanon): ABS {
        val gcVertIdx = gc.verts.indexOf(newOut)
        val canonIdx = gc.perm.indexOf(gcVertIdx)
        val scVertIdx = sc.perm[canonIdx]
        val oldOut = sc.verts[scVertIdx]
        return oldOut
    }

    /** Adapt node [n] created with [sc] to the isomorphic new canon [gc]. */
    private fun adaptFromMemo(gc: GraphCanon, sc: GraphCanon, n: SNode): SNode {
        if (gc.orig.outs == n.schema.toABS()) return n
        val new2old = gc.orig.outs.map { it to findPairIndex(it, gc, sc) }
        assert(!new2old.all {(k,v) -> k==v})
        val i2old = new2old.mapIndexed { i, (_,o) -> AU(i) to o.a}.toMap()
        val i2new = new2old.mapIndexed { i, (n,_) -> AU(i) to n.a}.toMap()
        val u = makeUnbindAbove(n, i2old)
        return makeBindAbove(u, i2new)
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
        val u = makeUnbindAbove(n, i2old)
        return makeBindAbove(u, i2new)
    }
}



class SPlanEnumerate3(initialRoots: Collection<SNode>) {
    private val _origRoots = initialRoots.toList()
    constructor(vararg inputs: SNode) : this(inputs.asList())
    private val LOG = LogFactory.getLog(SPlanEnumerate3::class.java)!!
    companion object {
        private const val CHECK_BETWEEN_EXPAND = true
        // todo - configuration parameters for whether to expand +, prune, etc.
        private const val SOUND_PRUNE_TENSOR_INTERMEDIATE = true
        private const val UNSOUND_PRUNE_MAX_DEGREE = true
    }

    private val remainingToExpand = HashSet(initialRoots)
    //    private val seen = HashSet<Id>()
//    private val ht: BiMap<Hash, SNode> = HashBiMap.create()
    private val memo: CanonMemo = CanonMemo()
    private val attrPosListMemo = mutableMapOf<Id, List<AB>>()
    private val basesForExpand = mutableSetOf<SNode>()
//    private val planCost = PlanCost()



    fun expandAll() {
        while( remainingToExpand.isNotEmpty() )
            expand()
        elimianteExcessRoots()
    }

    private fun elimianteExcessRoots() {
        val roots = mutableSetOf<SNode>()
        val memo = mutableSetOf<SNode>()
        basesForExpand.forEach { getRootsAbove(it, memo, roots) }
        roots -= _origRoots
        roots.forEach { stripDead(it) }
    }

    private fun expand() {
        expand(remainingToExpand.removeFirst() ?: return)
        if (CHECK_BETWEEN_EXPAND)
            SPlanValidator.validateSPlan(_origRoots, true, false)
    }

    private fun expand(node: SNode) {
//        if( node in ht.values ) // todo replace with visit flag
//            return

        when( node ) {
            is SNodeData, is SNodeExt -> return node.inputs.forEach { expand(it) }
            is SNodeUnbind -> return expand(node.input)
            is SNodeBind -> return expand(node.input)
            is OrNode -> return // OrNodes are already expanded.
            is ENode -> throw AssertionError("unexpected ENode")
            is SNodeAggregate -> if (node.op != Hop.AggOp.SUM ) return expand(node.input)
            is SNodeNary -> if (node.op != SNodeNary.NaryOp.MULT && node.op != SNodeNary.NaryOp.PLUS) {
               return node.inputs.indices.forEach { expand(node.inputs[it]) }
            }
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
        var base = getBase(node)
        val attrPosList = SHash.createAttributePositionList(node, attrPosListMemo)
        // if the base has bound schema, then set the base to an Unbind above the base. Postcondition: base is unbound.
        if (base.schema.names.any { it.isBound() }) {
            base = makeUnbindAbove(base, attrPosList.filter { it in base.schema }.mapIndexed { i,a -> AU(i) to a }.toMap())
        }
        basesForExpand += base
        val verts = attrPosList.map { ABS(it, node.schema[it]!!) }
        return Edge.C(base, verts)
    }

    private fun getBase(node0: SNode): SNode {
        var node = node0
        while (node is SNodeBind || node is SNodeUnbind) {
            if (node.parents.isEmpty())
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
        if (LOG.isTraceEnabled)
            LOG.trace("factorPlus B=$b")
        val alts: Set<SNode> = mutableSetOf<SNode>().also{ factorPlusRec(listOf(), b.groupSame(), listOf(), 0, 1, 0, it, mutableSetOf()) }
        val r = optionOrNode(alts)
        memo.memoize(b, r)
        return r
    }

    private fun <T> List<T>.groupSame() = this.groupBy { it }.flatMap { it.value }


    /**
     * [Bold] and [Bcur] should be ordered so that identical items appear consecutively.
     * [depth] is frontier #; advances when i and j finish in a frontier.
     *
     * Output parameter: [alts], the alternatives for computing the GraphBag of [Bold]+[Bcur]+[Bnew].
     */
    private fun factorPlusRec(Bold: GraphBag, Bcur: GraphBag, Bnew: GraphBag, i0: Int, j0: Int, depth: Int,
                              alts: MutableSet<SNode>, factorPlusMemo: MutableSet<Rep>) {
        if (Bcur.isEmpty() && Bnew.isEmpty()) {
            if (LOG.isTraceEnabled)
                LOG.trace("finish+: $Bold")
            factorPlusBase(Bold).tryApply { alts += it }
            return
        }
        val (i,j) = run {
            // This section prevents enumerating the same factorizations multiple times.
            // If an item at position i (or j) is the same as the one before it that we chose NOT to factor out,
            // then don't repeat that choice. Move to the next different item instead.
            var i = i0; var j = j0
            while(i < Bcur.size) {
                while (i > 0 && i < Bcur.size && Bcur[i-1] == Bcur[i]) { i++; j = i+1 }
                while (j > i+1 && j < Bcur.size && Bcur[j - 1] == Bcur[j]) j++
                while (j > Bcur.size && j < Bcur.size + Bold.size && Bold[j - Bcur.size - 1] == Bold[j - Bcur.size]) j++
                if (j >= Bcur.size + Bold.size) {
                    i++; j = i+1
                } else break
            }
            i to j
        }
        if (i >= Bcur.size || i == Bcur.size-1 && Bold.isEmpty())
            return factorPlusRec((Bold + Bcur).groupSame(), Bnew.groupSame(), listOf(), 0, 1, depth+1, alts, factorPlusMemo)
        if (LOG.isTraceEnabled)
            LOG.trace("depth=$depth, i=$i, j=$j\n\tBold=$Bold\n\tBcur=$Bcur\n\tBnew=$Bnew")
        // 1. Explore not factoring common terms
        factorPlusRec(Bold, Bcur, Bnew, i, j+1, depth, alts, factorPlusMemo)
        // 2. Explore factoring out
        val Gi = Bcur[i]
        val Gj = if (j < Bcur.size) Bcur[j] else Bold[j-Bcur.size]
        for ((Gf: Graph, hi: Monomorph, hj: Monomorph) in enumPlusFactor(Gi, Gj)) {
            if (Gf.edges.isEmpty()) continue
            checkPlusFactorization(Gf, hi, Gi)
            checkPlusFactorization(Gf, hj, Gj)
            val Bp = mutableListOf<Graph>()
            // if factoring out results in a single edge and it is a factored graphbag, then add all its graphs to Bp
            // otherwise add the graph resulting from factoring out
            Bp += factorOutTerms(Gf, hi, Gi) // lines 11 to 19
            Bp += factorOutTerms(Gf, hj, Gj)

            val Op = Bp.outs()
            if (SOUND_PRUNE_TENSOR_INTERMEDIATE && Op.size > 2) continue

            // put output vertices in order of canonical graph order - ensures compatibility with enumPlusFactor so that it can be factored out later
            val BpSortedC = memo.canonize(Bp).orderCanon()
            val BpEdge = Edge.F(BpSortedC.orig, BpSortedC.orderOuts())
            val Gp = Graph(Gi.outs+Gj.outs, Gf.edges + BpEdge)

            val newBold: GraphBag; val newBcur: GraphBag
            if (j < Bcur.size) { newBold = Bold; newBcur = Bcur - Gi - Gj }
            else { newBold = Bold - Gj; newBcur = Bcur - Gi }
            val newBnew: GraphBag = Bnew + Gp

            // new term formed. See if we already explored this form.
            if (depth >= 1) {
                val newB: GraphBag = newBold + newBcur + newBnew
                val newBcannon = memo.canonize(newB)
                if (newBcannon.rep in factorPlusMemo) continue
                else factorPlusMemo += newBcannon.rep
            }
            // we did not explore this factoring yet
            factorPlusRec(newBold, newBcur, newBnew, i, i+1, depth, alts, factorPlusMemo)
        }
//        return optionOrNode(alts)
    }

    private fun enumPlusFactor(g1: Graph, g2: Graph): Iterator<Triple<Graph, Monomorph, Monomorph>> {
        return EnumPlusFactorAdapter(EnumPlusFactor(g1, g2))
    }

    private fun factorOutTerms(Gf: Graph, h: Monomorph, G: Graph): List<Graph> {
        val Ep = G.rename(h.invert()).edges - Gf.edges
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
        val alts = mutableSetOf<SNode>()
        for ((B1, B2) in enumPartition(B)) {
            val r1 = factorPlusBase(B1).toNode() ?: continue
            val r2 = factorPlusBase(B2).toNode() ?: continue // if this is None, then r1 will be dangling. It will be removed after expandAll()
            alts += makePlusAbove(r1, r2)
        }
//        if (alts.isEmpty()) undo(B)
        val r = optionOrNode(alts)
        memo.memoize(B, r)
        return r
    }

    private fun <T> enumPartition(l: List<T>): Iterator<Pair<List<T>,List<T>>> {
        val (listOrdered, przs) = orderGenPrz(l)
        return EnumPartition(listOrdered, przs)
    }

    /**
     * Given a list with duplicates grouped consecutively and marked by [przs],
     * iterate over the partitionings of the list into two nonempty subsets, such that every partitioning is enumerated exactly once.
     */
    class EnumPartition<T>(val l: List<T>, val przs: List<PrefixRejectZone>): AbstractIterator<Pair<List<T>, List<T>>>() {
        // detect when some elements in list are equal; don't enumerate the same state more than once
        private var iter = PrefixRejectTopIter(l.size, 1, przs)
        init { setNext(computeSubset()) }

        private fun computeSubset(): Pair<List<T>, List<T>> {
            val t = iter.top()!!
            return l.partitionIndexed { (i, _) -> i in t }
        }

        override fun computeNext() {
            if (iter.next() != null) {
                // break symmetry on exact half split - don't enumerate same set twice
                return if (l.size % 2 == 0 && iter.n == l.size/2 && iter.top()!![0] != 0) done()
                else setNext(computeSubset())
            }
            if (iter.n+1 > l.size/2)
                return done()
            iter = PrefixRejectTopIter(l.size, iter.n+1, przs)
            return setNext(computeSubset())
        }
    }

    private fun factorAgg(g: Graph): SNodeOption {
        if (g.aggs.isEmpty()) return factorMult(g.edges)
        memo.adaptFromMemo(g)?.let { return it }
        val partitions: List<Graph> = partitionByAggCC(g)
        if (partitions.size > 1) {
            val createdNodes = mutableSetOf<SNode>()
            val ep = mutableListOf<Edge>()
            partitions.forEach { p ->
                if (p.edges.size == 1 && p.aggs.isEmpty())
                    ep += p.edges[0]
                else {
                    val l = factorAgg(p)
                    memo.memoize(p, l)
                    when (l) {
                        SNodeOption.None -> return@forEach
                        is SNodeOption.Some -> createdNodes += l.node
                    }
                    val gc = memo.canonize(p)
                    ep += Edge.F(listOf(p), gc.orderVertsCanon(p.outs))
                }
            }
            if (ep.size != partitions.size) { // one of the Edges failed (None from factorAgg)
//                createdNodes.forEach { undo(it) }
                return SNodeOption.None
            }
            val r = factorMult(ep)
            memo.memoize(g, r)
//            if (r == SNodeOption.None) {
////                createdNodes.forEach { undo(it) }
//            }
            return r
        }
        if (SOUND_PRUNE_TENSOR_INTERMEDIATE && g.outs.size > 2) return SNodeOption.None
        if (g.aggs.size == 1 || g.edgeGroups().size == 1) {
            val mult = factorMult(g.edges).toNode() ?: return SNodeOption.None
            val agg = makeAggAbove(mult, g.aggs.map(ABS::a).toSet())
            val r = agg.toOption()
            memo.memoize(g, r)
            return r
        }
        val aggsEnu = if (UNSOUND_PRUNE_MAX_DEGREE) {
            val dmap: Map<ABS, Int> = memo.canonize(g).v2ns.filterKeys { it in g.aggs }.mapValues { (_,v) -> v.size }
            val dmax = dmap.values.max()!!
            g.aggs.filter { dmap[it] == dmax }.toSet()
        } else g.aggs
        val alts = mutableSetOf<SNode>()
        for (v in aggsEnu) {
            val gbelow = Graph(g.outs + v, g.edges)
            val below = factorAgg(gbelow)
            below.tryApply { alts += makeAggAbove(it, v.a) }
        }
        val r = optionOrNode(alts)
        memo.memoize(g, r)
        return r
    }

    private fun partitionByAggCC(g: Graph): List<Graph> {
        val aggOneHop = g.buildOneHopMapUndirected(g.aggs)
        val aggCCs = findCCs(aggOneHop, g.aggs)
        val g0 = run {
            val e0 = g.edges.filter { it.verts.disjoint(g.aggs) }
            val o0 = e0.flatMap { it.verts }.toSet()
            Graph(o0, e0)
        }
        val gs = aggCCs.map { aggCC ->
            val ei = g.edges.filter { !it.verts.disjoint(aggCC) }
            val oi = g.outs.intersect(ei.flatMap { it.verts })
            Graph(oi, ei)
        }
        return if (g0.edges.isEmpty()) gs else gs+g0
    }

    private fun factorMult(es: List<Edge>): SNodeOption {
        // TODO - memo for edges - not as complicated as Graphs
        //if (useMemo) memo.adaptFromMemo(es)?.let { return it }
        if (es.isEmpty()) return memo.literalOne.toOption()
        if (es.size == 1) {
            val e = es[0]
            return when (e) {
                is Edge.C -> {
                    val tgtMap = e.verts.mapIndexed{i,abs -> AU(i) to abs.a}.toMap()
                    makeBindAbove(e.base, tgtMap).toOption()
                }
                is Edge.F -> {
                    val opt = factorPlusBase(e.base)
                    if (e.verts.size < 2) opt
                    else opt.map { n ->
                        // transpose if necessary
                        val actual = SHash.createAttributePositionList(n, attrPosListMemo)
                        val expect = e.verts.map(ABS::a)
                        if (expect == actual) n
                        else {
                            // todo make sure this is working
                            val tgt = expect.mapIndexed { i, a -> AU(i) to a }.toMap()
                            val u = makeUnbindAbove(n, tgt)
                            makeBindAbove(u, tgt)
                        }
                    }
                }
            }
        }
        val alts: MutableSet<SNode> = mutableSetOf()
        for ((es1, es2) in enumPartition(es)) {
            if (SOUND_PRUNE_TENSOR_INTERMEDIATE &&
                    (es1.flatMap(Edge::verts).toSet().size > 2 || es2.flatMap(Edge::verts).toSet().size > 2))
                continue
            val r1 = factorMult(es1).toNode() ?: continue
            val r2 = factorMult(es2).toNode() ?: continue // if this is None, then r1 will be dangling. It will be removed after expandAll()
            alts += makeMultAbove(r1, r2)
        }
//        if (alts.isEmpty()) undo(es)
        val r = optionOrNode(alts) // if size 0, indicates dangling nodes.
//        if (useMemo) memo.memoize(es, r)
        return r
    }



    private fun optionOrNode(alts: Set<SNode>): SNodeOption {
        val sNodeOption = when (alts.size) {
            0 -> SNodeOption.None
            1 -> alts.single().toOption()
            else -> OrNode(alts).toOption() //be careful about flattening - maybe it is okay. Check if a lower OrNode has pointers to it from the memo table; if so, need to rewire to top OrNode.
        }
        return sNodeOption
    }

}


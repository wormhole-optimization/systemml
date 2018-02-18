package org.apache.sysml.hops.spoof2.enu2

import org.apache.sysml.hops.LiteralOp
import org.apache.sysml.hops.spoof2.GraphBagCanon
import org.apache.sysml.hops.spoof2.GraphCanon
import org.apache.sysml.hops.spoof2.GraphCanonizer
import org.apache.sysml.hops.spoof2.SHash
import org.apache.sysml.hops.spoof2.plan.*
import java.util.ArrayList
import kotlin.math.roundToInt

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
internal fun SNode.toOption() = SNodeOption.Some(this)

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
fun <T> List<T>.getDuplicated(): Set<T> {
    return this.groupBy { it }.filter { (_,b) -> b.size > 1 }.map { (a,_) -> a }.toSet()
}

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
            val bindings = verts.mapIndexed { i, v -> Attribute.Unbound(i) to v.a }.toMap()
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
    fun getBases(): Set<SNode> {
        return edges.flatMap { e ->
            when (e) {
                is Edge.C -> listOf(e.base)
                is Edge.F -> e.base.flatMap { it.getBases() }
            }
        }.toSet()
    }
}

//data class GraphBag(val graphs: List<Graph>) {
//    fun isCanonical() = graphs.all(Graph::isCanonical)
//}

internal fun checkPlusFactorization(Gf: Graph, h: Monomorph, G: Graph) {
    check(h.keys.map(ABS::a).noDups()) {"h is a relation, not a function; duplicate name in keys of $h"}
    check(h.values.map(ABS::a).noDups()) {"h is not 1-1; duplicate name in values of $h"}
//    check(h.values.size == h.values.toSet().size) {"h is not 1-1: $h"}
    for (v in Gf.verts) {
        check(v in h) {"h is a partial function; undefined on input $v: $h"}
        val vp = h[v]!!
        check(v.s == vp.s) {"h maps an index to a different shape: $v to $vp"}
        check(vp in G.verts) {"h maps $v to $vp which is not in G: $G"}
        if (v in Gf.outs) {
            check(vp == v) {"non-stationary output under h: $v maps to $vp"}
            check(vp in G.outs) {"output index $v maps to non-output index $vp under $h for Gf $Gf to G $G"}
        }
        else {
            check(G.verts.none { it.a == v.a }) {"non-fresh agg. index $v; overlaps with graph $G"}
            check(vp !in G.outs) {"aggregated index $v maps to non-aggregated index $vp under $h for Gf $Gf to G $G"}
        }
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

    private var repToNode_access = 0L
    private var repToNode_hit = 0L

    /** If [b] was previously explored and a node was memoized representing its alternatives,
     * then adapt the node to the output indices of [b] and return it.
     * Returns an [SNodeOption] if it is in the memo (whose node is adapted if the option is Some).
     * Returns null if the canonical form of [b] is not in the memo. */
    fun adaptFromMemo(b: GraphBag): SNodeOption? {
        val bc = canonize(b)
        if (bc.rep in ntb) repToNode_hit++
        countAccess()
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
        if (gc.rep in ntg) repToNode_hit++
        countAccess()
        return ntg[gc.rep]?.let { (sc, no) ->
            no.map {
                //                if (it !in it.inputs[0].parents) { // restore parents
//                    it.inputs.forEach { inp -> inp.parents += it }
//                }
                adaptFromMemo(gc, sc, it)
            }
        }
    }

    private fun countAccess() {
        repToNode_access++
        if (repToNode_access % 2000L == 0L)
            println("repToNode hit rate: $repToNode_hit/$repToNode_access = ${(repToNode_hit.toDouble()/repToNode_access * 100).roundToInt()}%")
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


fun GraphBag.connectedComponents(): List<GraphBag> {
    val bases = mutableListOf<MutableSet<SNode>>()
    val components = mutableListOf<MutableList<Graph>>()
    loop@for (g in this) {
        val gb = g.getBases().filter { it.schema.isNotEmpty() } // exclude scalar bases
        for (i in bases.indices) {
            if (!gb.disjoint(bases[i]) || gb.isEmpty() && bases[i].isEmpty()) { // empty case
                components[i].add(g)
                bases[i].addAll(gb)
                continue@loop
            }
        }
        components.add(mutableListOf(g))
        bases.add(gb.toMutableSet())
    }
    return components
}
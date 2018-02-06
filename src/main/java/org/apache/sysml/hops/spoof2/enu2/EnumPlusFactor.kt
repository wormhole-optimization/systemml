package org.apache.sysml.hops.spoof2.enu2

import com.google.common.collect.BiMap
import com.google.common.collect.HashBiMap
import com.google.common.collect.ImmutableBiMap
import org.apache.sysml.hops.spoof2.enu2.PrefixRejectTopIter.PrefixRejectZone
import org.apache.sysml.hops.spoof2.enu2.PrefixRejectTopIter.PrefixRejectZone.Companion.orderGenPrz
import org.apache.sysml.hops.spoof2.plan.AB
import org.apache.sysml.hops.spoof2.plan.map
import org.apache.sysml.hops.spoof2.plan.zipIntersect

//private typealias MatchingChoice = Pair<IntArray,IntArray>
private typealias V = ABS
private typealias VMap = BiMap<V,V>
data class SubgraphIso(val vertMap: VMap, val edgeMap: List<Pair<Edge,Edge>>)

class EnumPlusFactor(val g1: Graph, val g2: Graph) : TopIterator<SubgraphIso> {
    private sealed class AggStatus {
        object Agg: AggStatus() {
            override fun toString() = "Agg"
        }
        data class NoAgg(val outVert: V): AggStatus() {
            override fun toString() = "NoAgg($outVert)"
        }
    }
    private data class BaseAggStats(val base: Any, val aggStats: List<AggStatus>)
    // the PRZs signify identical edges. No point in considering them twice.
    private class Matching(val bas: BaseAggStats, val es1: List<Edge>, val es2: List<Edge>,
                           val prz1: List<PrefixRejectZone>, val prz2: List<PrefixRejectZone>
    ): TopIterator<List<Pair<Edge, Edge>>> {
        val maxFactorOut = minOf(es1.size, es2.size)
        private var iter = PairPrefixRejectTopIter(0, es1.size, es2.size, prz1, prz2)
        private fun setIterator(n: Int) {
            iter = PairPrefixRejectTopIter(n, es1.size, es2.size, prz1, prz2)
        }
        override fun reset() { setIterator(0) }
        override fun next(): List<Pair<Edge, Edge>>? {
            iter.next()
            return top()
        }
        override fun top(): List<Pair<Edge, Edge>>? {
            var t = iter.top()
            while (t == null && iter.n < maxFactorOut) { setIterator(iter.n+1); t = iter.top() }
            val (a1,a2) = t ?: return null
            return a1.indices.map { i -> es1[a1[i]] to es2[a2[i]] }
        }
    }

    private val arrMatch: List<Matching> = run {
        val map1 = buildMapBaseAggToEdges(g1)
        val map2 = buildMapBaseAggToEdges(g2)
        map1.zipIntersect(map2).map { (bas, p) ->
            // put alike values side-by-side
            val (g1, prz1) = orderGenPrz(p.first)
            val (g2, prz2) = orderGenPrz(p.second)
            Matching(bas, g1, g2, prz1, prz2)
        }
    }
//    private val arrIter: MutableList<PairPrefixRejectTopIter> = arrMatch.map { it.iterateChoices(0) }.toMutableList()
    private val arrVertMap: List<VMap>  = arrMatch.map { HashBiMap.create<V,V>() }
    private val vertMap: VMap = HashBiMap.create()
    /** If there are no Matchings, then this indicates whether the empty SubgraphIso has been enumerated yet. */
    private var iteratedEmpty = false

    override fun next(): SubgraphIso? {
        var si: SubgraphIso?
        do {
            var i = arrMatch.size - 1
            if (i == -1) {
                iteratedEmpty = true; return null
            }
            unassign(i)
            loop@ while (true) {
                while (true) {
                    while (arrMatch[i].next() == null) {
                        i--; if (i >= 0) unassign(i) else return null
                    }
                    while (!assign(i) && arrMatch[i].next() != null);
                    if (arrMatch[i].top() == null) {
                        i--; if (i >= 0) unassign(i) else return null
                        continue
                    }
                    break
                }
                for (j in i + 1 until arrMatch.size) {
                    arrMatch[j].reset()
                    if (!assign(j)) {
                        i = j
                        continue@loop
                    }
                }
                break
            }
            si = top()
        } while (si != null && acceptTop(si))
        return si
    }

    /**
     * Filter conditions on the subgraph isomorphisms accepted.
     * If false, don't emit the top one and call next instead.
     */
    private fun acceptTop(si: SubgraphIso): Boolean {
        return !PRUNE_ONLY_SCALAR || si.edgeMap.isEmpty() || si.vertMap.isNotEmpty() // reject non-trivial isomorphisms of only scalars
    }


    /** Atomically assign arrMatch[i] if possible, or if there is a conflict return false. */
    fun assign(i: Int): Boolean {
        val edgeMap = arrMatch[i].top() ?: return false
        val zip = edgeMap.flatMap { (e1,e2) ->
            assert(e1.verts.size == e2.verts.size)
            e1.verts.zip(e2.verts)
        }
        val (z1,z2) = zip.unzip()
        if(!z1.noDups()) return false
        if(!z2.noDups()) return false
        val lmap = zip.toMap().filter { (v1, v2) ->
            when {
                v1 in vertMap -> if(vertMap[v1] != v2) return false else false
                vertMap.containsValue(v2) -> return false
                else -> true
            }
        }
        vertMap.putAll(lmap)
        arrVertMap[i].putAll(lmap)
        return true
    }
    fun unassign(i: Int) {
        arrVertMap[i].forEach { (v1,v2) -> check(vertMap[v1] == v2); vertMap.remove(v1) }
        arrVertMap[i].clear()
    }

    override fun top(): SubgraphIso? {
        if (iteratedEmpty) return null
        val edgeMap = arrMatch.flatMap { match ->
            match.top() ?: return null
        }
        return SubgraphIso(vertMap, edgeMap)
    }

    override fun reset() {
        arrMatch.forEach { it.reset() }
        iteratedEmpty = false
    }


    companion object {
        /** Whether to prune non-trivial (at least one edge) subgraph isomorphisms that consist of only scalar edges. */
        const val PRUNE_ONLY_SCALAR = true


        private fun buildMapBaseAggToEdges(g: Graph): Map<BaseAggStats,List<Edge>> = g.edges.groupBy { e ->
            val aggStats = e.verts.map { v ->
                if (v in g.outs) AggStatus.NoAgg(v)
                else AggStatus.Agg
            }
            BaseAggStats(e.base, aggStats)
        }

        fun isoToNewGraphMonomorph(si: SubgraphIso, g1: Graph, g2: Graph): Triple<Graph,Monomorph,Monomorph> {
            val outs = mutableSetOf<V>()
            val (h1, h2) = si.vertMap.map { (v1, v2) ->
                val vn = if (v1 in g1.outs) {
                    assert(v1 == v2)
                    outs += v1; v1
                } else {
                    ABS(AB(v1.a), v1.s)
                }
                (vn to v1) to (vn to v2)
            }.unzip().map { ImmutableBiMap.copyOf(it.toMap()) }
            val edges = si.edgeMap.map { (e1,e2) ->
                assert(e1.base == e2.base)
                e1.rename(h1.inverse())
            }
            val gn = Graph(outs, edges)
            return Triple(gn, h1, h2)
        }
    }
}

class EnumPlusFactorAdapter(private val epf: EnumPlusFactor): AbstractIterator<Triple<Graph,Monomorph,Monomorph>>() {
    init { setNext(adapt(epf.top()!!)) }

    private fun adapt(si: SubgraphIso): Triple<Graph, Monomorph, Monomorph> {
        return EnumPlusFactor.isoToNewGraphMonomorph(si, epf.g1, epf.g2)
    }

    override fun computeNext() {
        setNext(adapt(epf.next() ?: return done()))
    }
}

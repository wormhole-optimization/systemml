package org.apache.sysml.hops.spoof2.enu2

import com.google.common.collect.BiMap
import com.google.common.collect.HashBiMap
import com.google.common.collect.ImmutableBiMap
import org.apache.sysml.hops.spoof2.enu2.PrefixRejectTopIter.PrefixRejectZone
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
            val (g1, prz1) = genEdgesPrz(p.first)
            val (g2, prz2) = genEdgesPrz(p.second)
            Matching(bas, g1, g2, prz1, prz2)
        }
    }
//    private val arrIter: MutableList<PairPrefixRejectTopIter> = arrMatch.map { it.iterateChoices(0) }.toMutableList()
    private val arrVertMap: List<VMap>  = arrMatch.map { HashBiMap.create<V,V>() }
    private val vertMap: VMap = HashBiMap.create()

    override fun next(): SubgraphIso? {
        var i = arrMatch.size-1
        unassign(i)
        loop@while(true) {
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
        return top()
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

    fun topSubIso(): SubgraphIso? {
        val edgeMap = arrMatch.flatMap { match ->
            match.top() ?: return null
        }
        return SubgraphIso(vertMap, edgeMap)
    }

    override fun top() = topSubIso()

    override fun reset() {
        arrMatch.forEach { it.reset() }
    }


    companion object {
        private fun buildMapBaseAggToEdges(g: Graph): Map<BaseAggStats,List<Edge>> = g.edges.groupBy { e ->
            val aggStats = e.verts.map { v ->
                if (v in g.outs) AggStatus.NoAgg(v)
                else AggStatus.Agg
            }
            BaseAggStats(e.base, aggStats)
        }
        private fun genEdgesPrz(edgesSameBase: List<Edge>): Pair<List<Edge>, List<PrefixRejectZone>> {
            val g1 = edgesSameBase.groupBy { it }.flatMap {
                it.value.mapIndexed { i, e -> e to i}
            }
            val prz1: MutableList<PrefixRejectZone> = mutableListOf()
            g1.foldIndexed(null as PrefixRejectZone?) { i, prz, (_,c) ->
                when {
                    c != 0 -> PrefixRejectZone(i-c, c)
                    prz == null -> null
                    else -> { prz1.add(prz); null }
                }
            }.let { if (it != null) prz1.add(it) }
            return g1.map{it.first} to prz1
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

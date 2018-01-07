package org.apache.sysml.hops.spoof2.enu2

import com.google.common.collect.BiMap
import com.google.common.collect.HashBiMap
import org.apache.sysml.hops.spoof2.enu2.PrefixRejectStream.PrefixRejectZone
import org.apache.sysml.hops.spoof2.plan.zipIntersect

//class EnumPlusFactor(val g1: Graph, val g2: Graph) : AbstractIterator<Triple<Graph, Monomorph, Monomorph>>() {
//    private sealed class AggStatus {
//        object Agg: AggStatus()
//        data class NoAgg(val outVert: ABS): AggStatus()
//    }
//    private data class BaseAggStats(val base: Any, val aggStats: List<AggStatus>)
//    // the PRZs signify identical edges. No point in considering them twice.
//    private data class Matching(val bas: BaseAggStats, val es1: List<Edge>, val es2: List<Edge>,
//                                val prz1: List<PrefixRejectZone>, val prz2: List<PrefixRejectZone>) {
//        val maxFactorOut = minOf(es1.size, es2.size)
//        fun iterateChoices(n: Int): Iterator<MatchingChoice> {
//            require(n <= maxFactorOut) {"n is $n but maxFactorOut is $maxFactorOut"}
//            val s1 = PrefixRejectStream(es1.size, n, prz1)
//            val s2 = PrefixRejectStream(es2.size, n, prz2)
//        }
//    }
//    private data class MatchingChoice(val c1: MutableList<Int> = mutableListOf(),
//                                      val c2: MutableList<Int> = mutableListOf())
//    private val arrMatch: List<Matching>
//    init {
//        val map1 = buildMapBaseAggToEdges(g1)
//        val map2 = buildMapBaseAggToEdges(g2)
//        arrMatch = map1.zipIntersect(map2).map { (bas, p) ->
//            // put alike values side-by-side
//            val (g1, prz1) = genEdgesPrz(p.first)
//            val (g2, prz2) = genEdgesPrz(p.second)
//            Matching(bas, g1, g2, prz1, prz2)
//        }
//    }
//
//
//
//    //    private data class VertCorr(val v1: ABS, val v2: ABS)
//    private val vertMap: BiMap<ABS, ABS> = HashBiMap.create()
////    private val arrNumIncl = IntArray(arrMatch.size) // 0 <= arrNumIncl[i] <= arrMatch[i].maxFactorOut
//    // each entry encodes which
//    private val arrChoice: List<MatchingChoice> = arrMatch.indices.map {MatchingChoice()}
//    private var nextFactoring: Triple<Graph, Monomorph, Monomorph>
//
//    init { // findFirst()
//        // starts at 000
//        // goto 100. If bad, goto 200. When maxed, goto 010. Then 110, 210, 020, 120, 220, 001, 101, ..., 222.
////        var ok = nextChoice(i)
//        for ((i,match) in arrMatch.withIndex()) {
//            val choice = arrChoice[i]
//            next
//        }
//    }
//
//    // todo - undo choice, new choice
//    private fun nextChoice(i: Int) {
//        // choice1, then choice2.
//        // When increasing choice*, go to the next one that has a different base (like bases are side-by-side).
//        val match = arrMatch[i]
//        val c = arrChoice[i]
//        var sz = c.c1.size
//        var changed = false
//        if (sz != 0) { // remove mapping from vertMap
//            vertMap[  ]
//        }
//        do {
//            match.es1
//            for (i1 in c.c1.indices.reversed()) {
//                val above = if (i1 == c.c1.size-1) c.c1.size else c.c1[i1+1]
//                if (c.c1[i1] < above-1) { c.c1[i1]++; changed=true; break }
//                else { c.c1[i1] = 0 }
//            }
//
//            // reset choice1; try to increase the indices in choice2
//        }
//    }
//    private fun nextChoiceI()
//
//
//    override fun computeNext() {
//        done()
//    }
//
//    companion object {
//        private fun buildMapBaseAggToEdges(g: Graph): Map<BaseAggStats,List<Edge>> = g.edges.groupBy { e ->
//            val aggStats = e.verts.map { v ->
//                if (v in g.outs) AggStatus.NoAgg(v)
//                else AggStatus.Agg
//            }
//            BaseAggStats(e.base, aggStats)
//        }
//        private fun genEdgesPrz(edgesSameBase: List<Edge>): Pair<List<Edge>, List<PrefixRejectZone>> {
//            val g1 = edgesSameBase.groupBy { it }.flatMap {
//                it.value.mapIndexed { i, e -> e to i}
//            }
//            val prz1: MutableList<PrefixRejectZone> = mutableListOf()
//            g1.foldIndexed(null as PrefixRejectZone?) { i, prz, (_,c) ->
//                when {
//                    c != 0 -> PrefixRejectZone(i-c, c)
//                    prz == null -> null
//                    else -> { prz1.add(prz); null }
//                }
//            }.let { if (it != null) prz1.add(it) }
//            return g1.map{it.first} to prz1
//        }
//    }
//}



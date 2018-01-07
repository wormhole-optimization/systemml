package org.apache.sysml.hops.spoof2.enu2

//class EnumPlusFactor(val g1: Graph, val g2: Graph) : Iterator<Triple<Graph, Monomorph, Monomorph>> {
//    private sealed class AggStatus {
//        object Agg: AggStatus()
//        data class NoAgg(val outVert: ABS): AggStatus()
//    }
//    private data class BaseAggStats(val base: Any, val aggStats: List<AggStatus>)
//    private data class Matching(val bas: BaseAggStats, val es1: List<Edge>, val es2: List<Edge>) {
//        val maxFactorOut = minOf(es1.size, es2.size)
//    }
//    private data class MatchingChoice(val c1: MutableList<Int> = mutableListOf(),
//                                      val c2: MutableList<Int> = mutableListOf()) {
//
//    }
//    private val arrMatch: List<Matching>
//    init {
//        val map1 = buildMapBaseAggToEdges(g1)
//        val map2 = buildMapBaseAggToEdges(g2)
//        arrMatch = map1.zipIntersect(map2).map { (bas, p) ->
//            // put alike values side-by-side
//            val g1 = p.first.groupBy { it }.flatMap { it.value }
//            val g2 = p.second.groupBy { it }.flatMap { it.value }
//            Matching(bas, g1, g2)
//        }
//    }
////    private data class VertCorr(val v1: ABS, val v2: ABS)
//    private val vertMap: MutableMap<ABS, ABS> = mutableMapOf()
////    private val arrNumIncl = IntArray(arrMatch.size) // 0 <= arrNumIncl[i] <= arrMatch[i].maxFactorOut
//    // each entry encodes which
//    private val arrChoice: List<MatchingChoice> = arrMatch.indices.map {MatchingChoice()}
//    private var nextFactoring: Triple<Graph, Monomorph, Monomorph>
//
//    init { // findFirst()
//        // starts at 000
//        // goto 100. If bad, goto 200. When maxed, goto 010. Then 110, 210, 020, 120, 220, 001, 101, ..., 222.
//        var ok = nextChoice(i)
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
//
//
//    override fun hasNext(): Boolean {
//        TODO("not implemented")
//    }
//
//    override fun next(): Triple<Graph, Monomorph, Monomorph> {
//        TODO("not implemented")
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
//    }
//}



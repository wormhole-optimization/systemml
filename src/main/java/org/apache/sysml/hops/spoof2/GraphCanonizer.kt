package org.apache.sysml.hops.spoof2

import org.apache.sysml.hops.spoof2.enu2.*
import org.apache.sysml.hops.spoof2.plan.Rep
import org.apache.sysml.hops.spoof2.plan.listComparator
import org.apache.sysml.hops.spoof2.plan.pairComparator
import org.apache.sysml.hops.spoof2.plan.permute

//private typealias C = Int
private typealias V = ABS
private typealias E = Edge

// The perm represents a Monomorph from the original graph's vertices to the canonical graph's vertices.
data class GraphCanon(val orig: Graph, val verts: List<V>,
                      val perm: List<Int>, val rep: Rep, val v2ns: Map<V,Set<V>>) {
    fun orderVertsCanon(vs: Set<V>): List<V> = vs.sortedBy { v -> perm[verts.indexOf(v)] }
}
data class GraphBagCanon(val orig: GraphBag, val vertCanons: List<GraphCanon>,
                         val perm: List<Int>, val rep: Rep) {
    /** Given an isomorphic graphbag [biso], return [biso] with graphs reordered to canonical order. */
    fun orderCanon() = GraphBagCanon(orig.permute(perm), vertCanons.permute(perm), perm.indices.toList(), rep)
//            orig.sortedBy { g ->
//        val idx = vertCanons.indexOfFirst { hash == it.hash }
//        perm[idx] // into canonical order
//    }
    /** Order the output indices based on the order of occurrence in [orig]'s order.
     * Consider calling [orderCanon] first to get the canonical order of graphs. */
    fun orderOuts(): List<V> {
        val outsRemain = HashSet(orig.outs())
        val res: MutableList<V> = mutableListOf()
        for (gc in vertCanons) {
            val g = gc.orig
            val outsHere = outsRemain.intersect(g.outs)
            outsRemain -= outsHere
            res += outsHere.sortedBy {
                gc.perm[gc.verts.indexOf(it)]
            }
        }
        assert(outsRemain.isEmpty())
        return res
    }
}



class GraphCanonizer(val graph: Graph, val memo: CanonMemo) {

    val elab: Map<Edge, Rep> = graph.edges.map { it to memo.canonize(it) }.toMap()
//    val v2c: MutableMap<V, C> = graph.verts.map { it to 0 }.toMap().toMutableMap()
//    val c2vs: MutableMap<C, MutableSet<V>> = mutableMapOf(1 to graph.verts.toMutableSet())
    val verts: List<V> = graph.verts.toList()
    val perm = verts.indices.toMutableList()
    val colorBars = BooleanArray(verts.size) // presence of bar starts a new color
    val colorToExpand = BooleanArray(verts.size) // which colors are in the queue
    val v2ns: Map<V, Set<V>> = graph.buildOneHopMapUndirected()
    val stillConfused: MutableList<SHash.IntSlice> = mutableListOf()

    private fun readCanonicalString(): Rep {
        // first 0-edges
        val (zeroEdges, regEdges) = graph.edges.partition { it.verts.isEmpty() }
        val s0 = zeroEdges.map { elab[it]!! }.sorted().joinToString(";") + "|" + graph.outs.size + "|"
        val newVertOrder = verts.permute(perm)
//        fun se(e: E): List<Int> {
//            return e.verts.map { newVertOrder.indexOf(it) }
//        }
        val sortEdges: (Edge) -> List<Int> = { it.verts.map { newVertOrder.indexOf(it) } }
        val sortEdgesList = regEdges.map(sortEdges).map { it.joinToString("_") }
        val perm = SHash.sortIndicesHierarchical(sortEdgesList, listOf({ it: String -> it }))
        // todo make it easier to get the sort indices
//        val f: java.util.function.Function<Edge, List<Int>> = sortEdges as java.util.function.Function<Edge, List<Int>> //{ it.verts.map { newVertOrder.indexOf(it) } }
//        val edgesSorted = regEdges.sortedWith(Comparator.comparing<Edge,List<Int>>(f, compareIntList))
        val edgesSorted = regEdges.permute(perm)
        return s0 + edgesSorted.joinToString("|") { elab[it] + "_" + edgeIncidenceString(newVertOrder, it) }
    }

    private fun edgeIncidenceString(vertOrder: List<V>, e: Edge): String {
        return vertOrder.joinToString(",") { e.verts.indexOf(it).toString() }
    }

    private fun initialColors() {
        val sortOutputFirst: (V) -> Boolean = { it !in graph.outs } // false is first
        // Concatenation of Sorted list of <Edge_label.position of each incident edge>.
        val s = verts.map { v ->
            v to elab.filterKeys { v in it.verts }
                    .map { (e,h) -> h to e.verts.indexOf(v) }
//                    .sortedWith(comparePairEdgeHash) // should I sort the string instead?
                    .map { (h,i) -> "$h.$i" }
                    .sorted()
                    .joinToString("_")
        }.toMap()
        val sortByEdge: (V) -> String = { s[it]!! }

        SHash.sortIndicesHierarchical(verts, listOf(sortOutputFirst), stillConfused, perm, null)
        addColorBars(0, perm.size-1) // mark those positions which are not confused
        val conf = ArrayList(stillConfused)
        stillConfused.clear()
        conf.forEach {
            SHash.sortIndicesHierarchical(verts, listOf(sortByEdge), stillConfused, perm, it.toRange().toList())
            addColorBars(it.first, it.last)
        }
//        println("stilConfused is $stillConfused")
    }

    fun canonize(): GraphCanon {
        initialColors()
        // todo - IR algorithm
        val canonicalString = readCanonicalString()
        return GraphCanon(graph, verts, perm, canonicalString, v2ns)
    }

    private fun addColorBars(first: Int, last: Int) {
        var i = first
        val iter = stillConfused.iterator()
        var next = if (iter.hasNext()) iter.next() else null
        while (i <= last) {
            while (next != null && next.last < i)
                next = if (iter.hasNext()) iter.next() else null
            when {
                next == null -> return colorBars.fill(true, i, last)
                i !in next -> {
                    colorBars.fill(true, i, minOf(next.first-1, last))
                    i = next.last+1
                }
                else -> i = next.last+1
            }
        }
    }


    companion object {
        val comparePairEdgeHash = pairComparator<Rep,Int>()
        val compareIntList = listComparator<Int>()
    }

}
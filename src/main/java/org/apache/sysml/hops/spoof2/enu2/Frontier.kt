package org.apache.sysml.hops.spoof2.enu2

import org.apache.commons.logging.LogFactory
import org.apache.log4j.Level
import org.apache.log4j.Logger
import org.apache.sysml.conf.DMLConfig
import org.apache.sysml.hops.spoof2.plan.fixedListOf
import org.apache.sysml.hops.spoof2.plan.removeFirst
import java.util.*

sealed class Frontier {
    private var _size = 0
    val size: Int
        get() = _size

    protected abstract fun _add(c: Construct)
    protected abstract fun _remove(c: Construct): Boolean
    protected abstract fun _popNextToExplore(): Construct
    fun isEmpty(): Boolean = size == 0
    fun isNotEmpty(): Boolean = size > 0

    fun add(c: Construct) {
        c.status = Construct.Status.FRONTIER
        _add(c)
        _size++
        if (CHECK_SIZE && this is OpeningBook)
            assert(size == this.manualSize()) {"size $size; manual ${this.manualSize()}"}
    }
    protected fun _addAll(cc: Collection<Construct>) = cc.forEach { _add(it) }
    fun remove(c: Construct): Boolean {
        c.status = Construct.Status.NONE
        val r = _remove(c)
        if (r) _size--
        if (CHECK_SIZE && this is OpeningBook)
            assert(size == this.manualSize()) {"size $size; manual ${this.manualSize()}"}
        return r
    }
    fun popNextToExplore(): Construct {
        val c = _popNextToExplore()
        c.status = Construct.Status.NONE
        _size--
        if (CHECK_SIZE && this is OpeningBook)
            assert(size == this.manualSize()) {"size $size; manual ${this.manualSize()}"}
        return c
    }
    
    companion object {
        private val LOG = LogFactory.getLog(BottomUpOptimize::class.java)!!
        private const val LDEBUG = DMLConfig.SPOOF_DEBUG
        init {
            if (LDEBUG) Logger.getLogger(Frontier::class.java).level = Level.TRACE
        }
        private const val CHECK_SIZE = false
    }

    class Smart : Frontier() {
        companion object {
            val orderConstructsToExploreFirst: Comparator<Construct> = Comparator { o1, o2 ->
                // Bases first: add all bases before doing anything else.
                // then most number of covered edges first
                // then smallest recCostNoShare / sum of nnz of included edges
                // then most CSE first: most CMaps before fewer CMaps
                // then by id: smallest ID first
                // Later add an active component that selects bases not yet filled in
                when {
                    o1.height == 0 && o2.height == 0 -> o1.id.compareTo(o2.id)
                    o1.height == 0 -> -1
                    o2.height == 0 -> 1
                    o1.maxCoveredEdges != o2.maxCoveredEdges -> -o1.maxCoveredEdges.compareTo(o2.maxCoveredEdges)
                    o1.recCostNoShare / o1.coveredBaseNnzSum != (o2.recCostNoShare / o2.coveredBaseNnzSum) ->
                        (o1.recCostNoShare / o1.coveredBaseNnzSum).compareTo(o2.recCostNoShare / o2.coveredBaseNnzSum)
                    o1.cmaps.size != o2.cmaps.size -> -o1.cmaps.size.compareTo(o2.cmaps.size)
                    else -> o1.id.compareTo(o2.id)
                }
            }
        }
        internal val exploreQueue: PriorityQueue<Construct> = PriorityQueue(orderConstructsToExploreFirst)

        override fun _add(c: Construct) {
            exploreQueue.add(c)
        }
        override fun _remove(c: Construct): Boolean {
            return exploreQueue.remove(c)
        }
        override fun _popNextToExplore(): Construct {
            return exploreQueue.remove()
        }
    }


    class Random : Frontier() {
        internal val storage: MutableList<Construct> = LinkedList()

        override fun _add(c: Construct) {
            storage.add(c)
        }
        override fun _remove(c: Construct): Boolean {
            return storage.remove(c)
        }
        override fun _popNextToExplore(): Construct {
            val idx = (Math.random() * size).toInt()
            return storage.removeAt(idx)
        }
    }

    class OpeningBook(val tgs: TargetGraphs, val nextFrontier: Frontier) : Frontier() {
        private val numTgts: Int = tgs.tgts.size
        private val bases: PriorityQueue<Construct.Base> = PriorityQueue(compareByNnz)
        private val aggs: MutableList<Construct.Agg> = mutableListOf()
        private val completeMap: List<PriorityQueue<Construct>> = fixedListOf(numTgts) { PriorityQueue(compareByCost) }
        private val emultMap: List<PriorityQueue<Construct.EWiseMult>> = fixedListOf(numTgts) { PriorityQueue(compareByNnz as Comparator<Construct.EWiseMult>) }
        private val mxmMap: List<PriorityQueue<Construct.MatrixMult>> = fixedListOf(numTgts) { PriorityQueue(compareByInputNnz as Comparator<Construct.MatrixMult>) }
        private val exploredCoveredEdgeMap: List<MutableSet<Int>> = fixedListOf(numTgts, ::mutableSetOf)
        private val reserveMap: List<MutableSet<Construct>> = fixedListOf(numTgts, ::mutableSetOf)
        private var finished = false

        companion object {
//            private fun isSubsetOfAny(b: BooleanArray, l: List<BooleanArray>): Boolean = l.any { b2 ->
//                b.withIndex().all { (i,v) -> !v || b2[i] }
//            }
//            private fun removeSubsetsOf(b: BooleanArray, l: MutableList<BooleanArray>) = l.removeIf { b2 ->
//                b2.withIndex().all { (i,v) -> !v || b[i] }
//            }
            private val compareByCost: Comparator<Construct> = compareBy { it.recCost }
            private val compareByNnz: Comparator<Construct> = compareBy { it.nnz }
            private val compareByInputNnz: Comparator<Construct> = compareBy { it.children.minBy { it.nnz }?.nnz ?: 0L }
        }

        // if cmap is complete, add it to complete. Return complete first

        override fun _add(c: Construct) {
            if (finished) 
                return nextFrontier._add(c)
            when (c) {
                is Construct.Base -> bases.add(c)
                is Construct.Agg -> aggs.add(c)
                is Construct.EWiseMult -> c.cmaps
                        .distinctBy { it.tgtGraph }
                        .forEach {
                            if (it.complete) completeMap[it.tgtGraph].add(c)
                            else emultMap[it.tgtGraph].add(c)
                        }
                is Construct.MatrixMult -> c.cmaps
                        .distinctBy { it.tgtGraph }
                        .forEach {
                            if (it.complete) completeMap[it.tgtGraph].add(c)
                            else mxmMap[it.tgtGraph].add(c)
                        }
                else -> throw AssertionError()
            }
        }

        override fun _remove(c: Construct): Boolean {
            return if (finished) nextFrontier._remove(c)
            else when (c) {
                is Construct.Base -> bases.remove(c)
                is Construct.Agg -> aggs.remove(c)
                is Construct.EWiseMult -> c.cmaps.fold(false) { acc, it -> emultMap[it.tgtGraph].remove(c) || acc }
                is Construct.MatrixMult -> c.cmaps.fold(false) { acc, it -> mxmMap[it.tgtGraph].remove(c) || acc }
                else -> false
            } or completeMap.fold(false) { acc, it -> it.remove(c) || acc } or // todo - some needless removal
                    reserveMap.fold(false) { acc, it -> it.remove(c) || acc }
        }

        override fun _popNextToExplore(): Construct {
            if (finished) return nextFrontier._popNextToExplore()
            if (tgs.bestComplete != null) {
                transferConstructs()
                finished = true
                return nextFrontier._popNextToExplore()
            }
            val r = bases.poll() ?:
                    findRemove(completeMap)?:
                    aggs.removeFirst()?:
                    findRemove(emultMap)?:
                    findRemove(mxmMap)?:
                    findRemove(reserveMap)?:
                    throw AssertionError("somehow ran out of constructs in Frontier Opening Book")
            _remove(r)
            return r
        }

        private fun findRemove(ma: List<MutableCollection<out Construct>>): Construct? {
            for ((i, q) in ma.withIndex()) {
                if (tgs.invComplete[i].isNotEmpty())
                    continue
                if (ma === completeMap || ma === reserveMap)
                    if (q.isEmpty())
                        continue
                    else
                        return q.removeFirst()
                val iter = q.iterator()
                while (iter.hasNext()) {
                    val c = iter.next()
                    // if c is okay, then remove and return it. Otherwise remove it and put it in the reserves.
                    iter.remove()
                    val ok = c.cmaps.any { it.tgtGraph == i && Arrays.hashCode(it.coveredEdges) !in exploredCoveredEdgeMap[i] }
                    if (ok) {
                        c.cmaps.forEach {
                            if (!it.complete)
                                exploredCoveredEdgeMap[it.tgtGraph].add(Arrays.hashCode(it.coveredEdges))
                        }
                        return c
                    } else {
                        reserveMap[i].add(c)
                    }
                }
            }
            return null
        }

        fun manualSize(): Int {
            if (finished)
                return when (nextFrontier) {
                    is Smart -> nextFrontier.exploreQueue.size
                    is Random -> nextFrontier.storage.size
                    else -> throw AssertionError()
                }
            val s = mutableSetOf<Construct>()
            s.addAll(bases)
            s.addAll(aggs)
            completeMap.forEach { s.addAll(it) }
            emultMap.forEach { s.addAll(it) }
            mxmMap.forEach { s.addAll(it) }
            reserveMap.forEach { s.addAll(it) }
            return s.size
        }

        private fun transferConstructs() {
            assert(bases.isEmpty())
            val s = mutableSetOf<Construct>()
            s.addAll(aggs); aggs.clear()
            completeMap.forEach { s.addAll(it); it.clear() }
            emultMap.forEach { s.addAll(it); it.clear() }
            mxmMap.forEach { s.addAll(it); it.clear() }
            reserveMap.forEach { s.addAll(it); it.clear() }
            nextFrontier._addAll(s)
        }
    }

}

typealias EdgeList = List<Edge.C>
typealias VMap<T> = Map<ABS, T>



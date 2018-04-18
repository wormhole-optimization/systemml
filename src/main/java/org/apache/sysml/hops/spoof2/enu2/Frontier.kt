package org.apache.sysml.hops.spoof2.enu2

import org.apache.commons.logging.LogFactory
import org.apache.log4j.Level
import org.apache.log4j.Logger
import org.apache.sysml.conf.DMLConfig
import org.apache.sysml.hops.spoof2.plan.listOfEmptyLists
import org.apache.sysml.hops.spoof2.plan.removeFirst
import org.apache.sysml.hops.spoof2.plan.removeLast
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
    }
    protected fun _addAll(cc: Collection<Construct>) = cc.forEach { _add(it) }
    fun remove(c: Construct): Boolean {
        c.status = Construct.Status.NONE
        val r = _remove(c)
        if (r) _size--
        return r
    }
    fun popNextToExplore(): Construct {
        val c = _popNextToExplore()
        c.status = Construct.Status.NONE
        _size--
        return c
    }
    
    companion object {
        private val LOG = LogFactory.getLog(BottomUpOptimize::class.java)!!
        private const val LDEBUG = DMLConfig.SPOOF_DEBUG
        init {
            if (LDEBUG) Logger.getLogger(Frontier::class.java).level = Level.TRACE
        }
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
        private val exploreQueue: PriorityQueue<Construct> = PriorityQueue(orderConstructsToExploreFirst)

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
        private val storage: MutableList<Construct> = LinkedList()

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
        private val complete: MutableSet<Construct> = mutableSetOf()
        private val aggMap: List<MutableList<Construct.Agg>> = listOfEmptyLists(numTgts)
        private val emultMap: List<MutableList<Construct.EWiseMult>> = listOfEmptyLists(numTgts)
        private val mxmMap: List<MutableList<Construct.MatrixMult>> = listOfEmptyLists(numTgts)
        private val coveredEdges: List<MutableList<BooleanArray>> = listOfEmptyLists(numTgts)
        private var finished = false
        private val other: MutableSet<Construct> = mutableSetOf()

        companion object {
            private fun isSubsetOfAny(b: BooleanArray, l: List<BooleanArray>): Boolean = l.any { b2 ->
                b.withIndex().all { (i,v) -> !v || b2[i] }
            }
            private fun removeSubsetsOf(b: BooleanArray, l: MutableList<BooleanArray>) = l.removeIf { b2 ->
                b2.withIndex().all { (i,v) -> !v || b[i] }
            }
            private val compareByNnz: Comparator<Construct> = compareBy { it.nnz }
        }

        // if cmap is complete, add it to complete. Return complete first

        override fun _add(c: Construct) {
            if (finished) 
                return nextFrontier._add(c)
            c.cmaps.find(CMap::complete)?.let { comp ->
                coveredEdges[comp.tgtGraph].clear()
                coveredEdges[comp.tgtGraph] += comp.coveredEdges
                complete += c
                return
            }
            when (c) {
                is Construct.Base -> bases.add(c)
                is Construct.Agg -> c.cmaps.forEach {
                    aggMap[it.tgtGraph].add(c)
                }
                is Construct.EWiseMult -> c.cmaps
                        .filter { !isSubsetOfAny(it.coveredEdges, coveredEdges[it.tgtGraph]) }
                        .let { cmaps ->
                            if (cmaps.isEmpty()) {
                                other.add(c)
                                if (LOG.isTraceEnabled)
                                    LOG.trace("~deferred $c")
                            } else cmaps.forEach {
                                emultMap[it.tgtGraph].add(c)
                                removeSubsetsOf(it.coveredEdges, coveredEdges[it.tgtGraph])
                                coveredEdges[it.tgtGraph] += it.coveredEdges
                            }
                        }
                        
                is Construct.MatrixMult -> c.cmaps
                        .filter { !isSubsetOfAny(it.coveredEdges, coveredEdges[it.tgtGraph]) }
                        .let { cmaps ->
                            if (cmaps.isEmpty()) {
                                other.add(c)
                                if (LOG.isTraceEnabled)
                                    LOG.trace("~deferred $c")
                            } else cmaps.forEach {
                                mxmMap[it.tgtGraph].add(c)
                                removeSubsetsOf(it.coveredEdges, coveredEdges[it.tgtGraph])
                                coveredEdges[it.tgtGraph] += it.coveredEdges
                            }
                        } 
                else -> {
                    other.add(c)
                    if (LOG.isTraceEnabled)
                        LOG.trace("~deferred $c")
                }
            }
        }

        override fun _remove(c: Construct): Boolean {
            return if (finished) nextFrontier._remove(c)
            else when (c) {
                is Construct.Base -> bases.remove(c)
                is Construct.Agg -> c.cmaps.fold(false) { acc, it -> aggMap[it.tgtGraph].remove(c) || acc }
                is Construct.EWiseMult -> c.cmaps.fold(false) { acc, it -> emultMap[it.tgtGraph].remove(c) || acc }
                is Construct.MatrixMult -> c.cmaps.fold(false) { acc, it -> mxmMap[it.tgtGraph].remove(c) || acc }
                else -> false
            } or complete.remove(c) or other.remove(c)
        }

        override fun _popNextToExplore(): Construct {
            if (finished) return nextFrontier._popNextToExplore()
            if (tgs.bestComplete != null) {
                transferConstructs()
                finished = true
                return nextFrontier._popNextToExplore()
            }
            val r = bases.poll() ?:
                    complete.removeFirst()?:
                    aggMap.find { it.isNotEmpty() }?.removeFirst()?:
                    emultMap.find { it.isNotEmpty() }?.removeFirst()?:
                    mxmMap.find { it.isNotEmpty() }?.removeFirst()?: throw AssertionError()
            _remove(r)
            return r
        }

        private fun transferConstructs() {
            assert(bases.isEmpty())
            val s = mutableSetOf<Construct>()
            s.addAll(complete); complete.clear()
            aggMap.forEach { s.addAll(it); it.clear() }
            emultMap.forEach { s.addAll(it); it.clear() }
            mxmMap.forEach { s.addAll(it); it.clear() }
            s.addAll(other); other.clear()
            nextFrontier._addAll(s)
        }
    }

}

typealias EdgeList = List<Edge.C>
typealias VMap<T> = Map<ABS, T>



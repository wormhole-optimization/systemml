package org.apache.sysml.hops.spoof2.enu2

import java.util.*

sealed class Frontier {

    abstract val size: Int
    abstract fun add(c: Construct)
    abstract fun remove(c: Construct)
    abstract fun popNextToExplore(): Construct
    fun isEmpty(): Boolean = size == 0
    fun isNotEmpty(): Boolean = size > 0

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

        override val size: Int
            get() = exploreQueue.size
        override fun add(c: Construct) {
            exploreQueue += c
            c.status = Construct.Status.FRONTIER
        }
        override fun remove(c: Construct) {
            exploreQueue -= c
            c.status = Construct.Status.NONE
        }
        override fun popNextToExplore(): Construct {
            val c = exploreQueue.remove()
            c.status = Construct.Status.NONE
            return c
        }
    }


    class Random : Frontier() {
        private val storage: MutableList<Construct> = LinkedList()

        override val size: Int
            get() = storage.size
        override fun add(c: Construct) {
            storage += c
            c.status = Construct.Status.FRONTIER
        }
        override fun remove(c: Construct) {
            storage -= c
            c.status = Construct.Status.NONE
        }
        override fun popNextToExplore(): Construct {
            val idx = (Math.random() * size).toInt()
            val c = storage.removeAt(idx)
            c.status = Construct.Status.NONE
            return c
        }
    }

}

typealias EdgeList = List<Edge.C>
typealias VMap<T> = Map<ABS, T>



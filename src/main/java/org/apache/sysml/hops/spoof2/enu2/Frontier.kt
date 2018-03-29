package org.apache.sysml.hops.spoof2.enu2

import java.util.*

class Frontier {

    companion object {
        val orderConstructsToExploreFirst: Comparator<Construct> = Comparator { o1, o2 ->
            // Bases first: add all bases before doing anything else.
            // then depth first: taller height before shorter height
            // then smallest recCostNoShare / sum of nnz of included edges
            // then CSE first: most CMaps before fewer CMaps
            // then by id: smallest ID first
            // Later add an active component that selects bases not yet filled in
            when {
                o1.height == 0 && o2.height == 0 -> o1.id.compareTo(o2.id)
                o1.height == 0 -> -1
                o2.height == 0 -> 1
                o1.recCostNoShare / o1.coveredBaseNnzSum != (o2.recCostNoShare / o2.coveredBaseNnzSum) ->
                    (o1.recCostNoShare / o1.coveredBaseNnzSum).compareTo(o2.recCostNoShare / o2.coveredBaseNnzSum)
                o1.cmaps.size != o2.cmaps.size -> -o1.cmaps.size.compareTo(o2.cmaps.size)
                else -> o1.id.compareTo(o2.id)
            }
        }
    }
    private val exploreQueue: PriorityQueue<Construct> = PriorityQueue(orderConstructsToExploreFirst)
//    private val descendingCost: PriorityQueue<Construct> = PriorityQueue(compareBy { -it.recCost })

    val size: Int
        get() = exploreQueue.size


    fun add(c: Construct) {
        exploreQueue += c
        c.status = Construct.Status.FRONTIER
    }

    fun remove(c: Construct) {
        exploreQueue -= c
        c.status = Construct.Status.NONE
    }


    fun popNextToExplore(): Construct {
        require(isNotEmpty())
        val c = exploreQueue.remove()
        c.status = Construct.Status.NONE
        return c
    }

    fun printStats() {

    }

    fun isNotEmpty(): Boolean = exploreQueue.isNotEmpty()
    fun isEmpty(): Boolean = exploreQueue.isEmpty()
}

typealias EdgeList = List<Edge.C>
typealias VMap<T> = Map<ABS, T>



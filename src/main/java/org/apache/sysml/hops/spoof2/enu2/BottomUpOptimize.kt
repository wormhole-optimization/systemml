package org.apache.sysml.hops.spoof2.enu2

import java.util.*

class BottomUpOptimize(dogbs: DagOfGraphBags) {
    val nnzInfer: NnzInfer = NnzInfer(nnzInferer)

    init {
        _buo = this
    }

    val costQueue: PriorityQueue<Construct> = PriorityQueue(compareBy { -it.recCost })

    val frontier = Frontier()
    val tgs = TargetGraphs(dogbs)

    @Suppress("UNCHECKED_CAST")
    val initialBases: List<Edge.C> = tgs.tgtEdgeListNoScalars.flatten().distinctBy { it.base }

    fun drive() {
        initialBases.forEach { b ->
            val c = Construct.Base.NonScalar(b, nnzInfer.infer(b), tgs)
            frontier.add(c)
        }
        val startTime = System.currentTimeMillis()
        var counter = 0L
        var upperBound: Double = tgs.upperBound

        while (frontier.isNotEmpty()) {
            val con = frontier.popNextToExplore()
            // Track the newly derived constructs that are formed from exploring incomplete cmaps.
            // The ones formed from exploring complete cmaps are fully explored already.
            val derivedFromIncomplete = tgs.explore(con)
            derivedFromIncomplete.forEach { frontier.add(it) } // on add, updates upper bound and prunes if possible
            counter++

            if (upperBound != tgs.upperBound) {
                upperBound = tgs.upperBound
                // global prune
                while (costQueue.isNotEmpty() && costQueue.peek().isGlobalPruned()) {
                    costQueue.peek().prune()
                }
            }

            if (counter % 1000 == 0L && tgs.bestComplete != null) {
                val elapsed = System.currentTimeMillis() - startTime
                if (elapsed > MAX_DURATION_MS)
                    break
            }
        }

        // finished plan: tgs.bestComplete
        // sum these up in the best possible way using a heuristic.
        tgs.finish() // return

        _buo = null
    }



    companion object {
        val nnzInferer: NnzInferer = WorstCaseNnz
        private const val MAX_DURATION_MS = 20 * 1000

        private var _buo: BottomUpOptimize? = null
        /**
         * Global controller.
         */
        internal val buo: BottomUpOptimize
            get() = _buo!!
    }

}
package org.apache.sysml.hops.spoof2.enu2

import org.apache.commons.logging.LogFactory
import org.apache.log4j.Level
import org.apache.log4j.Logger
import org.apache.sysml.conf.DMLConfig
import java.io.File
import java.text.SimpleDateFormat
import java.util.*

class BottomUpOptimize(dogbs: DagOfGraphBags) {
    val nnzInfer: NnzInfer = NnzInfer(nnzInferer)

    init {
        _buo = this
    }

    val costQueue: PriorityQueue<Construct> = PriorityQueue(compareBy { -it.recCost })

    val stats = this.Statistics()

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
        stats.setStart(startTime)
        var counter = 0L
        var upperBound: Double = tgs.upperBound

        if (LOG.isTraceEnabled) {
            LOG.trace("tgts: \n\t${tgs.tgts.withIndex().joinToString("\n\t") { (i,g) -> "$i: $g"}}")
        }

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
                    val toprune = costQueue.peek()
                    if (LOG.isTraceEnabled) {
                        LOG.trace("Global prune [${toprune.status}]: $toprune")
                    }
                    toprune.prune()
                }
            }

            stats.logBuoIteration(counter)

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
        stats.close()
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

        private val LOG = LogFactory.getLog(BottomUpOptimize::class.java)!!
        private const val LDEBUG = DMLConfig.SPOOF_DEBUG
        init {
            if (LDEBUG) Logger.getLogger(BottomUpOptimize::class.java).level = Level.TRACE
        }

        internal const val PRUNE_FULLY_LOCAL = false

        private const val DO_STATS = true
        private const val STAT_FOLDER = "buo_stats"
        private const val STAT_FILE_PREFIX = "buo_stats_"
        private const val STAT_FILE_SUFFIX = ".tsv"

        private const val STAT_CUTOFF_MINITER = 10

        private val LOADUP_TIMESTAMP = SimpleDateFormat("yyyy-MM-dd-HH-mm-ss").format(Date()) // for millis, add -SSS
        private var globalStatsCounter = 0L
    }

    inner class Statistics : AutoCloseable {
        init {
            val folder = File(STAT_FOLDER)
            if (!folder.exists())
                folder.mkdir()
        }
        val statFileName = "$STAT_FOLDER/$STAT_FILE_PREFIX${LOADUP_TIMESTAMP}_${globalStatsCounter.toString().padStart(4, '0')}$STAT_FILE_SUFFIX"
        val statFile = File(statFileName)
        val statFileWriter = statFile.writer().buffered()

        init {
            val header = "iter\telapsed\tupperBound\tcreated\tglobalPruned\tlocalPruned\tfrontierSize\n"
            statFileWriter.write(header)
            globalStatsCounter++
        }

        var startTime = 0L
        var cntCreated = 0L
        var cntGlobalPruned = 0L
        var cntLocalPruned = 0L
        var longestIter = 0L

        fun logBuoIteration(iter: Long) {
            longestIter = iter
            val elapsed = System.currentTimeMillis() - startTime
            val frontierSize = frontier.size
            val upperBound = if (tgs.upperBound == Double.POSITIVE_INFINITY) 0L else tgs.upperBound.toLong()

            val s = "$iter\t$elapsed\t${upperBound.toStringNoZero()}\t${cntCreated}\t${cntGlobalPruned.toStringNoZero()}\t${cntLocalPruned.toStringNoZero()}\t$frontierSize\n"
            statFileWriter.write(s)
        }

        override fun close() {
            statFileWriter.close()
            if (longestIter < STAT_CUTOFF_MINITER) {
                // delete file; not worth keeping this one
                statFile.delete()
            } else {
                // rename file to include longestIter at the end of the file name
                val newName = statFileName.substring(0, statFileName.length - STAT_FILE_SUFFIX.length) + "-" + longestIter + STAT_FILE_SUFFIX
                statFile.renameTo(File(newName))

                // also include original graph and the bestComplete in a new, related file
                val graphFileName = statFileName.substring(0, statFileName.length - STAT_FILE_SUFFIX.length) + "-" + longestIter + "-graph.txt"
                val graphFile = File(graphFileName)
                graphFile.writer().buffered().use { graphFileWriter ->
                    graphFileWriter.write("Original Bases: \n\t${initialBases.joinToString("\n\t") { e -> "${e.base} -- ${e.base.schema} -- nnz ${nnzInfer.infer(e)}"}}\n\n")
                    graphFileWriter.write("Original GraphBags: \n\t${tgs.origDogbs.graphBags.withIndex().joinToString("\n\t") { (i,g) -> "$i: $g"}}\n")
                    graphFileWriter.write("bestComplete: \n\t${tgs.bestComplete!!.withIndex().joinToString("\n\t") { (i,g) -> "$i: $g"}}\n")
                    graphFileWriter.write("upperBound: ${tgs.upperBound}\n\n")
                    graphFileWriter.write("tgts: \n\t${tgs.tgts.withIndex().joinToString("\n\t") { (i,g) -> "$i: $g"}}\n")
                }
            }
        }

        fun logPrunedConstruct(global: Boolean) {
            if (global) cntGlobalPruned++
            else cntLocalPruned++
        }

        fun logCreatedConstruct() {
            cntCreated++
        }

        fun setStart(startTime: Long) {
            this.startTime = startTime
        }

        fun Long.toStringNoZero(): String = if (this == 0L) "" else this.toString()

    }


}
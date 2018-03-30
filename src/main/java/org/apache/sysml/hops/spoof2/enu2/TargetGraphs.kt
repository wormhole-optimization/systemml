package org.apache.sysml.hops.spoof2.enu2

import org.apache.commons.logging.LogFactory
import org.apache.log4j.Level
import org.apache.log4j.Logger
import org.apache.sysml.conf.DMLConfig
import org.apache.sysml.hops.LiteralOp
import org.apache.sysml.hops.spoof2.plan.*
import java.util.*

class TargetGraphs(
        val origDogbs: DagOfGraphBags,
        val buo: BottomUpOptimize
) {
    //val tgtPlus = origDogbs.graphBags
    val tgtMult: List<Graph>// may not need to actually store; size is # of ditinct graphs.
    val tgtPlusInclusion: List<IntArray> // size == origDogbs.graphBags.size. inner size == tgtMult.size. Value is the # of each of tgtGraph.
    val tgts: List<Graph> // size is # of distinct graphs after partitioning. Some are all-scalar graphs that have a single Construct for them. Some are same except they are transposes of each other.
    val tgtMultInclusion: List<IntArray> // size == tgtMult.size. inner size == tgts.size. Value is the # of each tgt to multiply together

    init {
        // fill tgtMult with distinct graphs among all the graphbags. Create arrays linking each graphbag to the # of each distinct graph.
        val (_t1, _t2) = origDogbs.graphBags.groupInnerWithOuterIndexDense()
        tgtMult = _t1
        tgtPlusInclusion = _t2

        // fill tgts with the distinct partitioned forms of the graphs in tgtMult. Create arrays linking each tgtMult graph to the # of each partitioned graph.
        val (_t3, _t4) = tgtMult.map { partitionn(it) }.groupInnerWithOuterIndexDense()
        tgts = _t3
        tgtMultInclusion = _t4
    }

    // partition edges by connected components; scalars in a separate component
    fun partitionn(_g: Graph): List<Graph> {
        val (g0, g) = run {
            val (e0, e) = _g.edges.partition { it.verts.isEmpty() }
            Graph(setOf(), e0) to Graph(_g.outs, e)
        }
        val oneHop = g.buildOneHopMapUndirected()
        val CCs = findCCs(oneHop, g.verts) // all vertices!
        val gs = CCs.map { CC ->
            val ei = g.edges.filter { !it.verts.disjoint(CC) }
            val ev = ei.flatMap { it.verts }
            val oi = g.outs.filter { it in ev }.toSet()
            Graph(oi, ei)
        }
        return if (g0.edges.isEmpty()) gs else gs+g0
    }


    // For each graph, the main edge list considered for constructions:
    @Suppress("UNCHECKED_CAST")
    val tgtEdgeListNoScalars: List<EdgeList> = tgts.map { tg ->
        tg.edges.filter { it.verts.isNotEmpty() } as List<Edge.C>
    }

    val tgtVertToAdjEdges: List<VMap<BooleanArray>> = tgts.mapIndexed { tgi, tg ->
        tg.verts.map { v -> v to BooleanArray(tgtEdgeListNoScalars[tgi].size) { v in tgtEdgeListNoScalars[tgi][it].verts }  }.toMap()
    }


    // For each graph, map from vertices to CMaps incident on them (in their outer schema)
    val invMaps: List<VMap<MutableList<CMap>>> =
            tgts.map { tg -> tg.verts.map { it to mutableListOf<CMap>() }.toMap() }
    val invComplete: List<MutableList<Construct>> = tgts.map { _ -> mutableListOf<Construct>() }
    val invCompleteMult: List<MutableList<Construct>> = tgtMult.map { _ -> mutableListOf<Construct>() }
    val invCompletePlus: List<MutableList<Construct>> = origDogbs.graphBags.map { _ -> mutableListOf<Construct>() }

    // one for each graph that we need to compute. Add functionality for + at a later time.
    var bestComplete: List<Construct>? = null
    var upperBound: Double = Double.POSITIVE_INFINITY
        //get() =  bestComplete?.recCost?.minus(COST_EPS) ?: Double.POSITIVE_INFINITY

    private val _scalarCache: MutableMap<Int, Construct> = mutableMapOf()
    fun getScalar(s: Int): Construct = _scalarCache.getOrPut(s) { Construct.Base.Scalar(buo, SNodeData(LiteralOp(s.toLong()))) }

    // initialize all-scalar graphs
    init {
        for ((i, tg) in tgts.withIndex()) {
            if (tg.edges.all { it.verts.isEmpty() }) {
                val cs = tg.edges.map { Construct.Base.Scalar(buo, it.toSNode()) as Construct }
                val c = if (cs.isEmpty()) getScalar(1)
                    else cs.subList(1,cs.size).fold(cs[0]) { acc, nexts ->
                        Construct.EWiseMult.construct(buo, acc, nexts, true)
                    }
                invComplete[i] += c
            }
        }
        // for each mult group, if it is filled, fill the invCompleteMult entry with the multiplication
        // for each plus group, if it is filled, fill the invCompletePlus entry with the addition
        // if all plus groups filled (all graphs are all scalars case), set bestComplete / upperBound
        f1@for ((multGroupIdx, multMultiplicities) in tgtMultInclusion.withIndex()) {
            // make sure we have at least one completed construct for all components
            for ((gi, m) in multMultiplicities.withIndex())
                if (m > 0 && invComplete[gi].isEmpty())
                    continue@f1
            // this mult group is filled
            val clist = multMultiplicities.mapIndexed { i, m ->
                if (m > 0) invComplete[i].single() else null
            }
            // checkPrune is false to avoid recursive initialization problem (leads to null pointer), and also nothing to check
            val multComplete = multAlignedConstructs(tgts, clist, multMultiplicities, false) ?: continue
            invCompleteMult[multGroupIdx] += multComplete
        }

        f2@for ((plusGroupIdx, plusMultiplicities) in tgtPlusInclusion.withIndex()) {
            // make sure we have at least one completed construct for all components
            for ((gi, m) in plusMultiplicities.withIndex())
                if (m > 0 && invCompleteMult[gi].isEmpty())
                    continue@f2
            // this plus group is filled
            val clist = plusMultiplicities.mapIndexed { i, m ->
                if (m > 0) invCompleteMult[i].single() else null
            }
            val plusComplete = plusConstructs(tgts, clist, plusMultiplicities, false) ?: continue
            invCompletePlus[plusGroupIdx] += plusComplete
        }

        if (invCompletePlus.all { it.isNotEmpty() }) {
            val flist = invCompletePlus.map { it.single() }
            val finalCost = combinedCost(flist)
            bestComplete = flist
            upperBound = finalCost
            // notify new upper bound?
        }
    }

    fun multAlignedConstructs(tgs: List<Graph>, _clist: List<Construct?>, multiplicities: IntArray,
                              checkPrune: Boolean): Construct? {
        return combineConstructs(tgs, _clist, multiplicities, checkPrune,
                { a, b -> a.makeOuterAbove(buo, b) }
        ) { _bg, _num -> recMult(buo, _bg, _num) }
    }

    fun plusConstructs(tgs: List<Graph>, _clist: List<Construct?>, multiplicities: IntArray,
                       checkPrune: Boolean): Construct? {
        return combineConstructs(tgs, _clist, multiplicities, checkPrune,
                { a, b -> a.makePlusAbove(buo, b) },
                this::multiplyScalar)
    }

    /** Multiply by scalar */
    private fun multiplyScalar(bg: Construct, num: Int): Construct {
        val c = getScalar(num)
        // todo: push into * of scalars if bg is an ewise and one of the inputs is the product of scalars
        return bg.makeAlignedEMultAbove(buo, c)
    }


    companion object {
        const val COST_EPS = 0

        private val LOG = LogFactory.getLog(TargetGraphs::class.java)!!
        private const val LDEBUG = DMLConfig.SPOOF_DEBUG
        init {
            if (LDEBUG) Logger.getLogger(TargetGraphs::class.java).level = Level.TRACE
        }

        // cost of executing all of these constructs, assuming maximum CSE sharing
        private fun combinedCost(clist: List<Construct>): Double {
            return clist.flatMap { it.recConstructsNoSelf + it }.toSet().sumByDouble { it.thisCost }
        }

        /* Returns null if the Construct' cost exceeds the upper bound.
         * list given in order of tgts */
        private inline fun combineConstructs(tgs: List<Graph>, _clist: List<Construct?>, multiplicities: IntArray,
                                             checkPrune: Boolean,
                                             combine: (Construct, Construct) -> Construct,
                                             doMulti: (Construct, Int) -> Construct): Construct? {
            require(_clist.size == multiplicities.size && tgs.size == _clist.size)
            val clist = _clist.mapIndexed { i, c ->
                val m = multiplicities[i]
                when (m) {
                    0 -> null
                    1 -> c
                    else -> doMulti(c!!, m) // todo use power
                }
            }

            val groups = tgs.zip(clist)
                    .filter { it.second != null }
                    .groupBy { (tg, c) -> tg.outs }
            val groupsSorted = groups.mapValues { (_, vals) ->
                vals.map { it.second!! }.sortedBy { it.nnz }
            }
            val groupsAdded = groupsSorted.mapValues { (schema, clist) ->
                clist.subList(1, clist.size).fold(clist[0]) { acc, nextc ->
                    val p: Construct = combine(acc, nextc)
                    if (checkPrune && p.isPruned()) {
                        p.prune()
                        return null
                    }
                    p
                }
            }
            val groupsAddedSorted = groupsAdded.toList().sortedByDescending { (schema, _) -> schema.size }.map {it.second}
            return groupsAddedSorted.subList(1, groupsAddedSorted.size).fold(groupsAddedSorted[0]) {acc, nextc ->
                val p: Construct = combine(acc, nextc)
                if (checkPrune && p.isPruned()) {
                    p.prune()
                    return null
                }
                p
            }
        }

        /** recursively add together [num] of [bg] (multiply) */
        private fun recAdd(buo: BottomUpOptimize, _bg: Construct, _num: Int): Construct {
            var num = _num
            var bg = _bg
            while (num > 1) {
                if (num % 2 == 0) {
                    bg = bg.makePlusAbove(buo, bg)
                    num /= 2
                } else {
                    bg = bg.makePlusAbove(buo, _bg)
                    num--
                }
            }
            return bg
        }

        /** recursively multiply together [num] of [bg] (power) */
        private fun recMult(buo: BottomUpOptimize, _bg: Construct, _num: Int): Construct {
            var num = _num
            var bg = _bg
            while (num > 1) {
                if (num % 2 == 0) {
                    bg = bg.makeAlignedEMultAbove(buo, bg)
                    num /= 2
                } else {
                    bg = bg.makeAlignedEMultAbove(buo, _bg)
                    num--
                }
            }
            return bg
        }
    }


    fun exploreComplete(_cons: CMap) {
        // (for each multiplication group,) combine with other complete constructs in the same multiplication group
        // add the newly formed ones to invCompleteMult and mark FINAL_MULT
        // (for each plus group,) for each newly formed one added to invCompleteMult, combine with other complete constructs in the same plus group
        // add the newly formed ones to bestComplete and mark FINAL_PLUS or FINAL_PLUS_MULT

        val tgtGraph = _cons.tgtGraph
        val construct = Construct.Rename(buo, _cons.construct, _cons.vertMap.map(ABS::a))
//                if (_cons.vertMap == tgts[tgtGraph].outs) _cons.construct
//                else _cons.construct.makeTransposeAbove().also { it.cmaps += _cons; it.status = Construct.Status.EXPLORED }

        invComplete[tgtGraph] += construct

        if (LOG.isTraceEnabled)
            LOG.trace("  invComplete[$tgtGraph]++; now ${invComplete.map { it.size }}")

        // these are the mult group index (for tgtMult and tgtMultInclusion and invCompleteMult)
        val multGroupIdxs = tgtMultInclusion.withIndex()
                .filter { (_, mi) -> mi[tgtGraph] > 0 }
                .map { (i, _) -> i }
        for (multGroupIdx in multGroupIdxs) {
            val multMultiplicities = tgtMultInclusion[multGroupIdx]
            // make sure we have at least one completed construct for all components
            if (multMultiplicities.withIndex().any { (gi, m) -> m > 0 && invComplete[gi].isEmpty() })
                continue

            if (LOG.isTraceEnabled) {
                val itercnt = multMultiplicities.withIndex().map { (gi, m) -> when {
                    gi == tgtGraph -> 1L
                    m == 0 -> 1L
                    else -> invComplete[gi].size.toLong()
                } }.prod()
                LOG.trace("  Complete multGroup $multGroupIdx with membership ${Arrays.toString(multMultiplicities)}. Will iterate $itercnt times")
            }

            // from invComplete,
            // returns a list of size tgts.size but with nulls at the positions where the tgtMultInclusion[multGroupIdx] has multiplicity 0
            // also, the construct at position cons.tgtGraph is always cons.construct
            val iterNewMultComplete: Iterator<List<Construct?>>
                    = enumConstructsWithNew(multMultiplicities, invComplete, construct, tgtGraph)
            for (mlist in iterNewMultComplete) {
                // for each one of these, multiply them together, respecting their multiplicities.
                // If the result is non-null (not pruned), then continue with adding it to invCompleteMult at index multGroupIdx.
                val _multComplete = multAlignedConstructs(tgts, mlist, multMultiplicities, true) ?: continue
                // todo - make sure there are no leaks of created and thown away constructs - properly prune which deletes from the parents array
                // Check Transpose!!
                val multComplete = _multComplete
//                        if (_multComplete.outer.size < 2) _multComplete
//                        else _multComplete.makeCheckTransposeAbove(tgtMult[multGroupIdx].outs)
                multComplete.status = Construct.Status.FINAL_MULT

                invCompleteMult[multGroupIdx] += multComplete

                if (LOG.isTraceEnabled)
                    LOG.trace("  invCompleteMult[$multGroupIdx]++; now ${invCompleteMult.map { it.size }}")

                // get all included plus groups
                val plusGroupIdxs = tgtPlusInclusion.withIndex()
                        .filter { (_, pi) -> pi[multGroupIdx] > 0 }
                        .map { (i, _) -> i }
                for (plusGroupIdx in plusGroupIdxs) {
                    val plusMultiplicities = tgtPlusInclusion[plusGroupIdx]
                    // make sure we have at least one completed construct for all components
                    if (plusMultiplicities.withIndex().any { (gi, m) -> m > 0 && invCompleteMult[gi].isEmpty() })
                        continue

                    if (LOG.isTraceEnabled) {
                        val itercnt = plusMultiplicities.withIndex().map { (gi, m) -> when {
                            gi == multGroupIdx -> 1L
                            m == 0 -> 1L
                            else -> invCompleteMult[gi].size.toLong()
                        } }.prod()
                        LOG.trace("   Complete plusGroup $plusGroupIdx with membership ${Arrays.toString(plusMultiplicities)}. Will iterate $itercnt times")
                    }

                    // similar; iterate over candidates in invCompleteMult at positions given by tgtPlusInclusion[plusGroupIdx]
                    // except for position multGroupIdx (use multComplete here)
                    // return a list of size tgtMult.size, with nulls at positions not covered re tgtPlusInclusion[plusGroupIdx]
                    val iterNewPlusComplete: Iterator<List<Construct?>>
                            = enumConstructsWithNew(plusMultiplicities, invCompleteMult, multComplete, multGroupIdx)
                    for (plist in iterNewPlusComplete) {
                        val plusComplete = plusConstructs(tgtMult, plist, plusMultiplicities, true) ?: continue

                        // we have a final fully summed construct for this bag, and it is not pruned.
                        plusComplete.status =
                                if (plusComplete.status == Construct.Status.FINAL_MULT)
                                    Construct.Status.FINAL_MULT_PLUS
                                else Construct.Status.FINAL_PLUS

                        invCompletePlus[plusGroupIdx] += plusComplete

                        if (LOG.isTraceEnabled)
                            LOG.trace("   invCompletePlus[$plusGroupIdx]++; now ${invCompletePlus.map { it.size }}")

                        // now, see if we can beat the best plan with this newly formed construct.
                        if (invCompletePlus.all { it.isNotEmpty() }) {
                            // no nulls in this one. Looks over invCompletePlus except for position plusGroupIdx (use plusComplete here)
                            val iterNewFinalComplete: Iterator<List<Construct>>
                                    = finalEnumConstructsWithNew(invCompletePlus, plusComplete, plusGroupIdx)
                            for (flist in iterNewFinalComplete) {
                                val finalCost = combinedCost(flist)

                                if (bestComplete == null || finalCost < upperBound) {
                                    if (LOG.isTraceEnabled)
                                        LOG.trace("    NEW final at cost $finalCost < $upperBound")
                                    bestComplete = flist
                                    upperBound = finalCost
                                } else {
                                    if (LOG.isTraceEnabled)
                                        LOG.trace("    Pruned final at cost $finalCost >= $upperBound")
                                }
                            }
                        } // end if invCompletePlus is all not empty
                    } // end for each way of adding candidates from invCompleteMult in the plus group
                } // end for each plus group
            } // end for each way of multiplying candidates from invComplete in the mult group
        } // end for each mult group
    }

    private fun finalEnumConstructsWithNew(invChoices: List<List<Construct>>,
                                           cons: Construct, tgtIdx: Int): Iterator<List<Construct>> {
        val ms = IntArray(invChoices.size) {1}
        val r = enumConstructsWithNew(ms, invChoices, cons, tgtIdx)
        @Suppress("UNCHECKED_CAST")
        return r as Iterator<List<Construct>>
    }

    // ms is multiplicities
    private fun enumConstructsWithNew(ms: IntArray, invChoices: List<List<Construct>>,
                                      cons: Construct, tgtIdx: Int): Iterator<List<Construct?>> {
        if (invChoices.size == 1)
            return listOf(listOf(cons)).iterator()
        // the indices to enumerate are those positions i in ms where ms[i] > 0 && i != tgtIdx
        // at positions i where ms[i] == 0, put null
        // at position i == tgtIdx, put cons.construct
        val idxsToIter = ms.withIndex()
                .filter { (i, m) -> m > 0 && i != tgtIdx }
                .map { (i,_) -> i }
        // limit of each index to iterate i is the size of invComplete[i]
        val limits = idxsToIter.map { invChoices[it].size }

        return object : Iterator<List<Construct?>> {
            private val enu = EnumerateIndices(limits.toIntArray())

            override fun hasNext(): Boolean = enu.hasNext()

            override fun next(): List<Construct?> {
                val x = enu.next()
                return invChoices.mapIndexed { i, clist ->
                    if (i == tgtIdx) cons
                    else {
                        val p = idxsToIter.indexOf(i)
                        if (p != -1) clist[x[p]] else null
                    }
                }
            }
        }
    }


    /**
     * 0. Check if pruned. Stop if pruned.
     * For each cmap of con,
     *
     * 1. If the cmap is incomplete, derive larger Constructs by examining neighbors in invMaps for EWise, MxM, or Agg.
     *        Add the larger ones to the frontier and to the invMaps.
     *    If the cmap is complete, combine it with other complete Constructs for the other graphs.
     *    --- Each derived construct is held with the CMaps that form it. Check derived constructs for pruning.
     *    --- Also discover sibling alternatives, that have the same outer schema and covered edges.
     * 2. Add the cmap to [invMaps] (incomplete) or [invComplete].
     */
    fun explore(con: Construct): Set<Construct> {
        if (con.isPruned()) {
            con.prune()
            return setOf()
        }
        con.status = Construct.Status.EXPLORED
        val derivedFromIncomplete: MutableSet<Construct> = mutableSetOf()
        if (LOG.isTraceEnabled)
            LOG.trace("EXPLORING: $con")

        for (cmapIdx in con.cmaps.indices) {
            val cmap = con.cmaps[cmapIdx]

            if (LOG.isTraceEnabled)
                LOG.trace(" CMAP $cmapIdx: $cmap ${if (cmap.complete) "complete" else ""}")

            if (cmap.complete) { // + with other DAGs
                exploreComplete(cmap)
            } else {
                val ok = exploreIncomplete(cmap, derivedFromIncomplete)
                if (!ok) {
                    do con.cmaps.removeAt(cmapIdx)
                    while (con.cmaps.size > cmapIdx)

                    con.prune() // handles derivedCons
                    return setOf()
                }
            }

            if (!cmap.complete) { // add cmap to invMaps
                val invMap = invMaps[cmap.tgtGraph]
                cmap.vertMap.forEach { v ->
                    invMap[v]!! += cmap
                } }
        }

        // fill in cmaps of all derived
        derivedFromIncomplete.forEach { it.fillCMaps() }
        return derivedFromIncomplete
    }


    // derivedCons will be cmap-instantiated afterward; just collect the constructs here
    // @return Whether to continue. If false, prune prune prune
    private fun exploreIncomplete(cmap: CMap, derivedFromIncomplete: MutableSet<Construct>): Boolean {
        val tg = tgts[cmap.tgtGraph]
        val tgtEdges = tgtEdgeListNoScalars[cmap.tgtGraph]
        val invMap = invMaps[cmap.tgtGraph]

        // 1. Check for siblings - have same covered edges, same outer schema
        // no need if we already linked cmap.construct to an existing sibling
        if (cmap.construct.siblings == null) {
            val sameOrientationAndCoveredEdges = // mapOuter -- cannot cache here because may prune
                    cmap.vertMap.map { v -> invMap[v]!! as List<CMap> }
                    .reduce { a, b -> a.intersect(b).toList() } // must be present on all same vertices
                    .filter {
                        it.vertMap == cmap.vertMap  // No reversal allowed!!
                                && Arrays.equals(it.coveredEdges, cmap.coveredEdges)
                    }
            if (sameOrientationAndCoveredEdges.isNotEmpty()) {
                if (LOG.isTraceEnabled)
                    LOG.trace("Found Siblings: $sameOrientationAndCoveredEdges")

                val rep = sameOrientationAndCoveredEdges.first().construct
                val alts = rep.siblings ?: mutableSetOf(rep).also { rep.siblings = it }
                alts += cmap.construct
                cmap.construct.siblings = alts

                if (cmap.construct.isLocallyPruned()) {
                    if (LOG.isTraceEnabled)
                        LOG.trace("Locally Pruned by Siblings!")
                    return false
                }
                cmap.construct.siblings!!.toList().forEach {
                    if (it.status != Construct.Status.PRUNED && it !== cmap.construct && it.isLocallyPruned(listOf(cmap.construct))) {
                        if (LOG.isTraceEnabled)
                            LOG.trace("A Sibling is locally pruned! $it")
                        it.prune()
                    }
                }
            }
        }

        val mapOuter = cmap.vertMap.map { v -> invMap[v]!! as List<CMap> }
        // only consider adjacent constructions that do not overlap on covered edges
        val mapOuterDisjoint = mapOuter.map {
            it.filter { cmap2 -> cmap2.coveredEdges.disjoint(cmap.coveredEdges) }
        }


        // 2. Check EWiseMult.
        mapOuterDisjoint.flatten().toSet().filter {bm ->
            val (smaller, larger) = if (bm.vertMap.size < cmap.vertMap.size) bm to cmap else cmap to bm
            smaller.vertMap.all { it in larger.vertMap }    // vertices must be a subset
//            && bm.coveredEdges.disjoint(cmap.coveredEdges)        // edges disjoint - already checked
        }.map { candidateCmap ->
            candidateCmap.construct to (cmap.vertMap.last() == candidateCmap.vertMap.last())
        }.toSet().mapNotNullTo(derivedFromIncomplete) { (candidate, aligned) ->
            val emult = cmap.construct.makeEMultAbove(buo, candidate, aligned)
            keepOrGlobalPrune(emult, derivedFromIncomplete)
        }

        if (cmap.vertMap.size == 2) { // ONLY MATRIX-MATRIX MXM
            val vertToAdjEdges = tgtVertToAdjEdges[cmap.tgtGraph]
            // 3. Check MxM.
            // for each incident vertex, see if it is a viable aggregated index in an MxM.
            // The vertex is viable if the vertex is not aggregated
            //   AND the candidate constructions aggregating on it cover all edges incident on it. (no tensors)
            // Then check that the non-matching vertices do not match
            //   and derive the appropriate MMType (matched vertex is on index of cmap.vertMap)
            cmap.vertMap.zip(mapOuterDisjoint).mapIndexed { aj, (vmatch, blist) ->
                val vmatchIncidentEdges = vertToAdjEdges[vmatch]!!

                val candidates = if (vmatch in tg.outs) listOf()
                else blist
                        .filter { it.vertMap.size == 2 } // ONLY MATRIX-MATRIX MXM
                        .map { bm ->
                    val bj = bm.vertMap.indexOf(vmatch) // matching vertex MMType aj-bj
                    val ok =
                            if (cmap.vertMap.size == 2 && bm.vertMap.size == 2
                                    && cmap.vertMap[other01(aj)] == bm.vertMap[other01(bj)])
                                false
                            else  // already checked for disjoint edges
                                vmatchIncidentEdges.coveredBy(cmap.coveredEdges, bm.coveredEdges)
                    if (ok) bm to bj
                    else null
                }.filterNotNull()

                candidates.mapNotNullTo(derivedFromIncomplete) { (bm, bj) ->
                    val mxm = cmap.construct.makeMxMAbove(buo, bm.construct, aj, bj)
                    keepOrGlobalPrune(mxm, derivedFromIncomplete)
                }
            }
        }


        // 4. Check Agg on either vertex.
        cmap.vertMap.filter { v ->
            v in tg.aggs && cmap.coveredEdges.withIndex().all { (ei, b) ->
                b || v !in tgtEdges[ei].verts
            }
        }.mapNotNullTo(derivedFromIncomplete) { v ->
            val agg = cmap.construct.makeAggAbove(buo, cmap.vertMap.indexOf(v))
            keepOrGlobalPrune(agg, derivedFromIncomplete)
        }

        return true
    }

    private fun keepOrGlobalPrune(c: Construct, dfi: Set<Construct>): Construct? {
        return if (c.isGlobalPruned()) {
            if (LOG.isTraceEnabled)
                LOG.trace("  PRUNED candidate: $c")
            c.prune()
            null
        }
        else {
            if (LOG.isTraceEnabled) {
                if (c in dfi)
                    LOG.trace("  Duplicate candidate: $c")
                else
                    LOG.trace("  Candidate: $c")
            }
            c
        }
    }


    fun finish() {
        if (LOG.isTraceEnabled)
            LOG.trace("FINAL BESTCOMPLETE: $bestComplete at cost $upperBound")
        check(bestComplete != null)

        // convert the bestComplete to SNodes and link them up to their parents
        for ((gbi, bc) in bestComplete!!.withIndex()) { // == bestComplete.indices
            val (rn, _) = bc.convertToSNode()

            val pa = origDogbs.graphBagParents[gbi]
            val paIdx = origDogbs.graphBagParentInputIndices[gbi]

            for (idx in pa.indices) {
                val p = pa[idx]
                val i = paIdx[idx]

                p.inputs.add(i, rn) // Orientation is okay?
                rn.parents.add(p)
            }
        }

    }
}
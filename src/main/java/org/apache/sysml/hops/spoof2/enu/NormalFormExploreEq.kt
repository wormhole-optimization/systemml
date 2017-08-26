package org.apache.sysml.hops.spoof2.enu

import org.apache.commons.logging.LogFactory
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.SPlanBottomUpRewriter
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriteRule.RewriteResult
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriter
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriter.RewriterResult
import org.apache.sysml.utils.Explain
import java.util.*
import java.util.concurrent.atomic.AtomicBoolean
import kotlin.collections.HashSet
import kotlin.collections.Map
import kotlin.collections.MutableSet
import kotlin.collections.Set
import kotlin.collections.any
import kotlin.collections.arrayListOf
import kotlin.collections.component1
import kotlin.collections.component2
import kotlin.collections.filter
import kotlin.collections.first
import kotlin.collections.flatMap
import kotlin.collections.forEach
import kotlin.collections.indices
import kotlin.collections.isNotEmpty
import kotlin.collections.listOf
import kotlin.collections.map
import kotlin.collections.mapIndexed
import kotlin.collections.min
import kotlin.collections.minus
import kotlin.collections.minusAssign
import kotlin.collections.mutableSetOf
import kotlin.collections.plusAssign
import kotlin.collections.sumBy
import kotlin.collections.toMap
import kotlin.collections.toSet

/**
 * Fill an E-DAG.
 */
class NormalFormExploreEq : SPlanRewriter {
    companion object {
        private val LOG = LogFactory.getLog(NormalFormExploreEq::class.java)!!
        private val statsAll = Stats()
        private val _addedHook = AtomicBoolean(false)
        private fun addHook() {
            if( !_addedHook.getAndSet(true) )
                Runtime.getRuntime().addShutdownHook(object : Thread() {
                    override fun run() {
                        if( LOG.isInfoEnabled )
                            LOG.info("Sum-Product all stats:\n\t$statsAll")
                    }
                })
        }
    }

    data class Stats(
            var numSP: Int = 0,
            var numInserts: Long = 0L,
            /** # of different agg, plus, multiply ops constructed */
            var numAggPlusMultiply: Long = 0L,
            var numLabels: Long = 0L,
            var numContingencies: Long = 0L,
            var considerPlan: Long = 0L
    ) {
        operator fun plusAssign(s: Stats) {
            numSP += s.numSP
            numInserts += s.numInserts
            numAggPlusMultiply += s.numAggPlusMultiply
            numLabels += s.numLabels
            numContingencies += s.numContingencies
            considerPlan += s.considerPlan
        }
        fun reset() {
            numSP = 0
            numInserts = 0
            numAggPlusMultiply = 0
            numLabels = 0
            numContingencies = 0
            considerPlan = 0
        }
    }


    val eNodes: ArrayList<ENode> = arrayListOf()
    var stats = Stats()
    val cseElim = SPlanBottomUpRewriter()


    override fun rewriteSPlan(roots: ArrayList<SNode>): RewriterResult {
        // for each sum-product block, place an ENode at the top
        // fill the ENode with different rewrites.
        // do CSE Elim and Bind Unify

        eNodes.clear()
        stats.reset()
        if( !_addedHook.get() )
            addHook()

        if( LOG.isTraceEnabled )
            LOG.trace("before normal form rewriting: "+Explain.explainSPlan(roots))

        do {
            val skip = HashSet<Long>()
            var changed = false // this could be due to a partitioning or a real Sum-Product block
            for (root in roots)
                changed = rRewriteSPlan(root, skip) || changed
            SNode.resetVisited(roots)
        } while( changed && eNodes.isEmpty() )

        if( eNodes.isEmpty() )
            return RewriterResult.NoChange

        if( LOG.isDebugEnabled )
            LOG.debug("$stats")
        if( LOG.isTraceEnabled )
            LOG.trace("E-DAG before CSE Elim: "+Explain.explainSPlan(roots))

        SPlanValidator.validateSPlan(roots)
        cseElim.rewriteSPlan(roots)

        // check inputs to ensure that CSE Elim did not change them
        eNodes.forEach { eNode ->
            for (i in eNode.ePaths.indices) {
                eNode.ePaths[i].input = eNode.inputs[i]
            }
        }

        doCosting(roots)

        if( LOG.isTraceEnabled )
            LOG.trace("E-DAG after implementing best plans: "+Explain.explainSPlan(roots))


//        // temporary replace with first such plan, whatever it is
//        eNodes.forEach { eNode ->
//            val chosenInput = eNode.inputs.first()
//            chosenInput.parents.addAll(eNode.parents)
//            eNode.parents.forEach { it.inputs[it.inputs.indexOf(eNode)] = chosenInput }
//            eNode.inputs.forEach {
//                it.parents -= eNode
//                stripDead(it)
//            }
//        }

        statsAll += stats
        return RewriterResult.NewRoots(roots)
    }

    private fun rRewriteSPlan(node: SNode, skip: HashSet<Long>): Boolean {
        if (node.visited)
            return false
        var changed = false

        for (i in node.inputs.indices) {
            var child = node.inputs[i]

            if( child.id !in skip) {
                val result = rewriteNode(child, skip)
                when (result) {
                    RewriteResult.NoChange -> {}
                    is RewriteResult.NewNode -> {
                        child = result.newNode
                        changed = true
                    }
                }
            }

            //process children recursively after rewrites
            changed = rRewriteSPlan(child, skip) || changed
        }

        node.visited = true
        return changed
    }

    private fun rewriteNode(node: SNode, skip: HashSet<Long>): RewriteResult {
        if( !SumProduct.isSumProductBlock(node))
            return RewriteResult.NoChange
//        val origSchema = Schema(node.schema)
        val spb = SumProduct.constructBlock(node, false)
        if( node.schema.names.any { !it.isBound() } )
            throw SNodeException(node, "Found unbound name in Sum-Product block; may not be handled incorrectly. $spb")
        if( LOG.isDebugEnabled )
            LOG.debug("Found Sum-Product Block:\n"+spb)

        // 0. Check if this normal form can be partitioned into two separate connected components.
        // This occurs if some portion of the multiplies produces a scalar.
        val CCnames = findConnectedNames(spb, spb.allSchema().names.first())
        if( CCnames != spb.allSchema().names.toSet() ) {
            val NCnames = spb.allSchema().names - CCnames

            val CCspb = SumProduct.Block(
                    spb.sumBlocks.map { SumBlock(it.op, it.names.filter { it in CCnames }) }
                            .filter { it.names.isNotEmpty() },
                    spb.product,
                    spb.edges.filter { it.schema.names.any { it in CCnames } }
                            .map { it.deepCopy() }
            )
            val NCspb = SumProduct.Block(
                    spb.sumBlocks.map { SumBlock(it.op, it.names.filter { it in NCnames }) }
                            .filter { it.names.isNotEmpty() },
                    spb.product,
                    spb.edges.filter { it.schema.names.any { it in NCnames } }
                            .map { it.deepCopy() }
            )
            spb.sumBlocks.clear()
            spb.edges.clear()
            spb.edges += CCspb
            spb.edges += NCspb
            spb.refresh()

            if( LOG.isDebugEnabled )
                LOG.debug("Partition Sum-Product block into disjoint components:\n" +
                        "Component 1: $CCspb\n" +
                        "Component 2: $NCspb")

            return RewriteResult.NewNode(spb.applyToNormalForm(node)) // these will be handled as disjoint sub-problems in SPlanNormalFormRewriter at next recursion
        }

        // Create ENode
        val eNode = ENode(node.schema)
        val bind = SNodeBind(eNode, node.schema.names.mapIndexed { i, n -> i to n }.toMap())
        node.parents.forEach { it.inputs[it.inputs.indexOf(node)] = bind }
        bind.parents.addAll(node.parents)
        eNodes += eNode
        // disconnect and dead code elim the input
        node.parents.clear() // can no longer use applyToNormalForm
//        stripDead(node, spb.getAllInputs()) // performed by constructBlock()

        // 1. Insert all paths into the E-DAG
        val numInserts = factorAndInsert(eNode, spb)
        if( LOG.isTraceEnabled )
            LOG.trace("numInserts: $numInserts")

//        // 2. CSE
//        SPlanBottomUpRewriter().rewriteSPlan(roots)

        stats.numSP++
        stats.numInserts += numInserts
        skip.addAll(eNode.inputs.flatMap { if(it is SNodeUnbind) listOf(it.id, it.input.id) else listOf(it.id) })
        return RewriteResult.NewNode(bind) //(bind)
    }

    /**
     * @return The number of inserts performed
     */
    private fun factorAndInsert(eNode: ENode, spb: SumProduct.Block): Int {
        if (spb.edgesGroupByIncidentNames().size == 1) {
            // all edges fit in a single group; nothing to do
            return insert(eNode, spb)
        }

        // 1. Multiply within groups
        spb.edgesGroupByIncidentNames().forEach { (_, edges) ->
            if (edges.size > 1) {
                // Create a Block on just these inputs.
                // Move these inputs to the new block and wire the new block to this block.
                // Push aggregations down if they are not join conditions (present in >1 edge).
                spb.factorEdgesToBlock(edges)
//                if (LOG.isTraceEnabled)
//                    LOG.trace("Isolating edge group\n[${edges.joinToString(",\n")}]")
            }
        }

        // Done if no aggregations remain
        if (spb.aggNames().isEmpty()) {
            return insert(eNode, spb)
        }

        // Determine what variables we could eliminate at this point
        val eligibleAggNames = spb.eligibleAggNames()
        // Prune down to the agg names with minimum degree
        val tmp = eligibleAggNames.map { it to (spb.nameToAdjacentNames()[it]!! - it).size }
        val minDegree = tmp.map { it.second }.min()!!
        check(minDegree <= 2) { "Minimum degree is >2. Will form tensor intermediary. In spb $spb" }
        val minDegreeAggNames = tmp.filter { it.second == minDegree }.map { it.first }

        // fork on the different possible agg names
        return minDegreeAggNames.sumBy { elimName ->
            val incidentEdges = spb.nameToIncidentEdge()[elimName]!!
            if( incidentEdges.size == spb.edges.size && spb.aggNames().isEmpty() ) { // if all edges remaining touch this one, nothing to do.
                insert(eNode, spb)
            } else {
                val factoredSpb = spb.deepCopy()
                factoredSpb.factorEdgesToBlock(incidentEdges)
                factorAndInsert(eNode, factoredSpb)
            }
        }
    }

    private fun insert(eNode: ENode, spb: SumProduct.Block): Int {
        val newTopInput = spb.constructSPlan().let { SNodeUnbind(it) }
        eNode.addNewEPath(newTopInput)
        stats.numAggPlusMultiply += spb.countAggsAndInternalBlocks()
        return 1
    }


    private fun findConnectedNames(spb: SumProduct.Block, name: Name): Set<Name> {
        return mutableSetOf<Name>().also { rFindConnectedNames(spb.nameToAdjacentNames(), name, it) }
    }

    /** Depth first search to find connected names. */
    private fun rFindConnectedNames(adjMap: Map<Name, Set<Name>>, name: Name, foundNames: MutableSet<Name>) {
        val adjacent = adjMap[name] ?: return
        val adjacentNotFound = adjacent - foundNames
        foundNames += adjacentNotFound
        adjacentNotFound.forEach { rFindConnectedNames(adjMap, it, foundNames) }
    }







    private fun doCosting(roots: ArrayList<SNode>) {
        for( root in roots )
            rMarkRooted(root)

        eNodes.sortBy { it.id } // ascending least id to greatest id
        for( eNode in eNodes ) {
            for( ePath in eNode.ePaths ) {
                // compute cost recursively, add this ePath to the labels of significant nodes (nodes with actual cost) along the way
                ePath.costNoContingent = rAddLabels(ePath.input, ePath, setOf())
            }
        }

        if( LOG.isTraceEnabled )
            LOG.trace("E-DAG after labeling: "+Explain.explainSPlan(roots))

        // all contingencies and costs computed.
        // Partition the ENodes into connected components.
        // Find the best EPath for each ENode individually and use this as a baseline.
        // Consider alternative EPaths that are locally suboptimal but allow sharing oppportunities.
        val CCs = partitionByConnectedComponent()
        if( LOG.isTraceEnabled )
            LOG.trace("CCs: "+CCs.map { it.map { it.id } })
        for( CC in CCs )
            findImplementBestPlanForCC(CC)
    }



    private fun rMarkRooted(node: SNode) {
        if( node.onRootPath )
            return
        if( node is ENode )
            return
        node.onRootPath = true
        node.inputs.forEach { rMarkRooted(it) }
    }

    private fun rAddLabels(node: SNode, ePath: EPath, overlappedEPaths: Set<EPath>): SPCost {
        return when {
            node.onRootPath -> {
                // do not include cost of nodes that are required to compute another root; these nodes are always shared
                // do not include recursive costs
                SPCost.ZERO_COST
            }
            node is ENode -> {
                // do not continue past ENode
                SPCost.ZERO_COST
            }
            node.cachedCost != SPCost.ZERO_COST -> {
                val newOverlapped = node.ePathLabels.filter { it.eNode != ePath.eNode && it !in overlappedEPaths }.toSet()
                val allOverlapped = if(newOverlapped.isNotEmpty()) overlappedEPaths + newOverlapped else overlappedEPaths
                val recCost = node.cachedCost + node.inputs.fold(SPCost.ZERO_COST) { acc, input -> acc + rAddLabels(input, ePath, allOverlapped) }

                val newOverlapList = newOverlapped.sortedBy { it.eNode.id }
                for( i in newOverlapList.indices ) {
                    val otherEPath = newOverlapList[i]
                    if( !ePath.contingencyCostMod.containsKey(otherEPath) ) // it could happen that we cross the same ePath in different branches
                        stats.numContingencies++
                    // if an overlappedEPath is selected, it shadows sharing this node.
                    // same story if an EPath from a different ENode also present here is picked.
                    ePath.contingencyCostMod.put(otherEPath,
                            EPath.EPathShare(otherEPath, recCost, node, overlappedEPaths + newOverlapList.subList(0, i)))
                }
                node.ePathLabels += ePath
                stats.numLabels++
                recCost
            }
            else -> {
                node.inputs.fold(SPCost.ZERO_COST) { acc, input -> acc + rAddLabels(input, ePath, overlappedEPaths) }
            }
        }
    }

    private fun partitionByConnectedComponent(): List<List<ENode>> {
        val CCs = ArrayList<List<ENode>>()
        val eNs = ArrayList(eNodes)
        do {
            val last = eNs.removeAt(eNs.size - 1)
            var newContingent = last.getContingentENodes()
            val recContingent = HashSet(newContingent)
            recContingent += last
            do {
                newContingent = newContingent.flatMap { it.getContingentENodes() }.toSet() - newContingent
                recContingent.addAll(newContingent)
            } while (newContingent.isNotEmpty())
            eNs.removeAll(recContingent)
            CCs += recContingent.sortedBy { it.id }
        } while( eNs.isNotEmpty() )
        return CCs
    }

    private fun findImplementBestPlanForCC(CC: List<ENode>) {
        // Consider contingencies
        val CCchoiceBest = ConsiderContingencies(CC, stats).findBestPlan()

        // Implement best plan
        implementPlan(CCchoiceBest)
    }

    /** Consider contingent plans for this connected component of ENodes.
     * @param CC The connected component. */
    class ConsiderContingencies(CC: List<ENode>, val stats: Stats) {
        private val num = CC.size
        private val nodes = CC.toTypedArray()
        private val nodeToIndex = nodes.mapIndexed { i, node -> node to i }.toMap()
        /** The EPaths that should be considered because they may reduce cost. */
        private val nodeContingencies = Array(num) { nodes[it].ePaths.filter { !it.contingencyCostMod.isEmpty } }
        /** The EPath-to-index map for [nodeContingencies] (caching). */
        private val nodeContingencyToIndex = Array(num) { nodeContingencies[it].mapIndexed { i, ePath -> ePath to i }.toMap() }
        /** 0 means that this EPath is allowed; >0 means that this EPath is blacklisted at that position. */
        private val nodeContingencyBlacklist = Array(num) { IntArray(nodeContingencies[it].size) }

        private val localCheapest = Array<EPath>(num) { nodes[it].ePaths.minBy { it.costNoContingent }!! }
        // inital best cost uses the lowest cost path for each ENode individually
        private val best = localCheapest.copyOf()
        private var bestTotalCost: SPCost = SPCost.MAX_COST
//        init {
//            var cum = SPCost.ZERO_COST
//            for( i in 0 until num) {
//                cum += localCheapest[i].costNoContingent
//                for( j in 0 until i) { // take advantage of any contingencies that happen to agree with our choice of path
//                    cum -= localCheapest[i].contingencyCostMod[localCheapest[j]]
//                            ?.fold(SPCost.ZERO_COST) { acc, (_,cost) -> acc + cost }
//                            ?: SPCost.ZERO_COST
//                }
//            }
//            bestTotalCost = cum
//        }
        private val choices = Array<EPath?>(num) {null}

        fun findBestPlan(): Array<EPath> {
            rConsiderContingency(num-1, SPCost.ZERO_COST)
            if( LOG.isTraceEnabled )
                LOG.trace("best plan found for CC ${nodes.map(ENode::id)}: " +
                        "${best.joinToString("\n\t", "\n\t", "\n\t")}@$bestTotalCost; $stats")
            return best
        }

        // pos: decreases from num-1 to -1
        // invariant: choices[pos+1 until num] != null (assigned)
        //            and choiceCumCost is the cummulative cost of those entries
        private fun rConsiderContingency(pos: Int, choiceCumCost: SPCost) {
            if( pos == -1 ) { // base case: we have a complete assignment
                if( choiceCumCost < bestTotalCost ) {
                    System.arraycopy(choices, 0, best, 0, num)
                    bestTotalCost = choiceCumCost
                }
                stats.considerPlan++
                return
            }
            val origChoice = choices[pos] // remember the current assignment so we can restore it later
            // origChoice is null if this position has not been fixed; non-null if it has been fixed
            if( origChoice != null && (origChoice.contingencyCostMod.isEmpty ||
                    nodeContingencyToIndex[pos][origChoice]!!.let { nodeContingencyBlacklist[pos][it] != 0 }) ) {
                // no contingencies for this fixed choice
                rConsiderContingency(pos-1, choiceCumCost + origChoice.costNoContingent)
                return
            }
            // If we did not fix an alternative from a past decision,
            // first try the cheap option, if we won't try it later during the contingencies
            if( origChoice == null && localCheapest[pos] !in nodeContingencies[pos] ) {
                choices[pos] = localCheapest[pos]
                rConsiderContingency(pos-1, choiceCumCost + localCheapest[pos].costNoContingent)
            }
            // Search over contingent ePaths for this fixed choice if we fixed it;
            // otherwise search over over all alternatives choices that are not blacklisted.
            val contingencyList =
                    if( origChoice != null ) listOf(origChoice)
                    else nodeContingencies[pos].filterIndexed { i, ePath ->
                        ePath == localCheapest[pos] || nodeContingencyBlacklist[pos][i] == 0
                    }
            for (chosenPath in contingencyList) {
                choices[pos] = chosenPath
                val (pathShares_groupByENode, fixedSavings) =
                        // cached in the EPath for efficiency; filter to those eNodes that are not yet fixed
                        // for those ENodes that are fixed, if they are fixed to a contingent path, then we save the contingent cost
                        chosenPath.pathShares_groupByENode().let { it ->
                            // partition the pathShares based on whether the ENode has been fixed yet
                            val (fixed, free)
                                    = it.partition { choices[nodeToIndex[it.first]!!] != null }

                            // for all pathShares under ENodes that have been fixed, see if we can reduce cost by sharing their path
                            // This method eliminates pathShares that overlap with another path share that is of >= cost savings
                            val fixedNonOverlap = EPath.filterNotOverlapping(chosenPath,
                                    fixed.flatMap {it.second.flatMap { it.second }})
                            val fixedSavings = fixedNonOverlap.fold(SPCost.ZERO_COST) { acc, pathShare ->
                                acc + pathShare.cost
                            }
                            free to fixedSavings
                        }

                val cSize = pathShares_groupByENode.size
                if( cSize == 0 ) {
                    rConsiderContingency(pos-1, choiceCumCost - fixedSavings + chosenPath.costNoContingent)
                    continue
                }
                if( cSize >= 62 )
                    LOG.warn("Huge number of contingent ENodes: $cSize. The next line may overflow Long.")
                val cSizeMax = (1 shl cSize) - 1
                var indicator = 0L
                val contPathChoiceIdx = IntArray(cSize)
                // loop over the choices of which eNodes we will fix, given by indicator
                do {
                    indicator++
                    // blacklist the contingent ePaths from each eNode we do not set
                    var t0 = 1L
                    for (j in 0 until cSize) {
                        if ((indicator and t0) == 0L) { // if we do not fix this eNode
                            val eNodeGroup = pathShares_groupByENode[j]
                            blacklistContingent(eNodeGroup.first, eNodeGroup.flatShares(), pos)
                            choices[nodeToIndex[eNodeGroup.first]!!] = null
                            contPathChoiceIdx[j] = -1 // for tracing
                        } else { // if we fix this eNode
                            contPathChoiceIdx[j] = 0
                        }
                        t0 = t0 shl 1
                    }

                    // loop over the choices of which contingent we will fix for each eNode that we decided to fix
                    while(true) {
                        var t = 1L
                        var changed = false
                        var cost = chosenPath.costNoContingent
                        // for each eNode, if we choose to fix that eNode, fix it and reduce the cost
                        for (j in 0 until cSize) {
                            val (contNode, contShares) = pathShares_groupByENode[j]

                            if ((indicator and t) != 0L) { // if we fix this eNode
                                // set this eNode to one of the contingent ePaths and reduce cost
                                val contShare = if (!changed) {
                                    if (contPathChoiceIdx[j] < contShares.size) {
                                        val x = contShares[contPathChoiceIdx[j]]
                                        contPathChoiceIdx[j]++
                                        changed = true
                                        x
                                    } else {
                                        contPathChoiceIdx[j] = 0
                                        contShares[0]
                                    }
                                } else if (contPathChoiceIdx[j] < contShares.size)
                                    contShares[contPathChoiceIdx[j]]
                                else
                                    contShares[0]

                                // check if this eNode is on the same path as another contingent cost
//                                testContShareOk(contShare, )
//                                if( contShare.shareNode.ePathLabels.filter {
//                                    it != chosenPath && it.eNode.id > contShare.ePath.eNode.id
//                                }.let { true } )

                                choices[nodeToIndex[contNode]!!] = contShare.first
                                cost -= contShare.sumShares()
                            }
                            t = t shl 1
                        }
                        if( changed )
                            rConsiderContingency(pos-1, choiceCumCost - fixedSavings + cost)
                        t = 1L
                        for (j in 0 until cSize) {
                            if ((indicator and t) != 0L) {
                                val (contNode, _) = pathShares_groupByENode[j]
                                choices[nodeToIndex[contNode]!!] = null
                            }
                            t = t shl 1
                        }
                        if( !changed )
                            break
                    }

                    // whitelist, undoing the blacklist
                    t0 = 1L
                    for (j in 0 until cSize) {
                        // todo optimize to see if changed in indicator+1
                        if ((indicator and t0) == 0L) { // if we do not fix this eNode
                            val eNodeGroup = pathShares_groupByENode[j]
                            whitelistContingent(eNodeGroup.first, eNodeGroup.flatShares(), pos)
                        }
                        t0 = t0 shl 1
                    }
                } while( indicator < cSizeMax )
            } // end for each ePath
            choices[pos] = origChoice
        } // end function


        // remove from consideration the ePaths present here,
        // because an upstream EPath was chosen not to be fixed even though there was a sharing opportunity
        private fun blacklistContingent(blackNode: ENode, blackEdges: List<EPath.EPathShare>, pos: Int) {
            val blackNodeIdx = nodeToIndex[blackNode]!!
            val ncti = nodeContingencyToIndex[blackNodeIdx]
            blackEdges.forEach {
                val blackEdge = it.ePath
                if( blackEdge in ncti ) {
                    val idx = ncti[blackEdge]!!
                    // if not already blacklisted at a higher level
                    if (nodeContingencyBlacklist[blackNodeIdx][idx] == 0)
                        nodeContingencyBlacklist[blackNodeIdx][idx] = pos
                }
            }
        }

        private fun whitelistContingent(blackNode: ENode, blackEdges: List<EPath.EPathShare>, pos: Int) {
            val blackNodeIdx = nodeToIndex[blackNode]!!
            val ncti = nodeContingencyToIndex[blackNodeIdx]
            blackEdges.forEach {
                val blackEdge = it.ePath
                if( blackEdge in ncti ) {
                    val idx = ncti[blackEdge]!!
                    if (nodeContingencyBlacklist[blackNodeIdx][idx] == pos)
                        nodeContingencyBlacklist[blackNodeIdx][idx] = 0
                }
            }
        }

    }

    private fun implementPlan(chosenPaths: Array<EPath>) {
        for( chosenPath in chosenPaths ) {
            val eNode = chosenPath.eNode
            val chosenInput = chosenPath.input
            chosenInput.parents.addAll(eNode.parents)
            eNode.parents.forEach { it.inputs[it.inputs.indexOf(eNode)] = chosenInput }
            eNode.inputs.forEach {
                it.parents -= eNode
                stripDead(it)
            }
        }

    }


}

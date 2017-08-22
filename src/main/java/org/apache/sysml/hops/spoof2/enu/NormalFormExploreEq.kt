package org.apache.sysml.hops.spoof2.enu

import org.apache.commons.logging.LogFactory
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.SPlanBottomUpRewriter
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriteRule.RewriteResult
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriter
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriter.RewriterResult
import org.apache.sysml.utils.Explain
import java.util.ArrayList
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
            var numContingencies: Long = 0L
    ) {
        operator fun plusAssign(s: Stats) {
            numSP += s.numSP
            numInserts += s.numInserts
            numAggPlusMultiply += s.numAggPlusMultiply
            numLabels += s.numLabels
            numContingencies += s.numContingencies
        }
        fun reset() {
            numSP = 0
            numInserts = 0
            numAggPlusMultiply = 0
            numLabels = 0
            numContingencies = 0
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

        val skip = HashSet<Long>()
        var changed = false
        for( root in roots)
            changed = rRewriteSPlan(root, skip) || changed
        SNode.resetVisited(roots)
        if( !changed )
            return RewriterResult.NoChange

        if( LOG.isDebugEnabled )
            LOG.debug("$stats")
        if( LOG.isTraceEnabled )
            LOG.trace("E-DAG before CSE Elim: "+Explain.explainSPlan(roots))

        SPlanValidator.validateSPlan(roots)
        cseElim.rewriteSPlan(roots)

        if( LOG.isTraceEnabled )
            LOG.trace("E-DAG before labeling: "+Explain.explainSPlan(roots))

        doCosting(roots)

        if( LOG.isTraceEnabled )
            LOG.trace("E-DAG after labeling: "+Explain.explainSPlan(roots))


        // temporary replace with first such plan, whatever it is
        eNodes.forEach { eNode ->
            val chosenInput = eNode.inputs.first()
            chosenInput.parents.addAll(eNode.parents)
            eNode.parents.forEach { it.inputs[it.inputs.indexOf(eNode)] = chosenInput }
            eNode.inputs.forEach {
                it.parents -= eNode
                stripDead(it)
            }
        }

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
                    RewriteResult.NoChange -> {
                    }
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
        // all contingencies and costs computed.
        // Partition the ENodes into connected components.
        // Find the best EPath for each ENode individually and use this as a baseline.
        // Consider alternative EPaths that are locally suboptimal but allow sharing oppportunities.
        val CCs = partitionByConnectedComponent()
        LOG.trace(CCs.map { it.map { it.id } })

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

                newOverlapped.forEach { otherEPath ->
//                    otherEPath.contingencyCostMod.put(ePath, node)
                    if( !ePath.contingencyCostMod.containsKey(otherEPath) )
                        stats.numContingencies++
                    ePath.contingencyCostMod.put(otherEPath, node to recCost)
                    Unit
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
}

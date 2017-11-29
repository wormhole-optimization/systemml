package org.apache.sysml.hops.spoof2.enu2

import com.google.common.collect.BiMap
import com.google.common.collect.HashBiMap
import org.apache.commons.logging.LogFactory
import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.spoof2.NormalFormHash
import org.apache.sysml.hops.spoof2.SPlan2NormalForm_InsertStyle
import org.apache.sysml.hops.spoof2.enu.ENode
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.RewriteBindElim.Companion.eliminateNode

class SPlanEnumerate(initialRoots: Collection<SNode>) {

    constructor(vararg inputs: SNode) : this(inputs.asList())

    // todo - configuration parameters for whether to expand +, prune, etc.
    private val remainingToExpand = HashSet(initialRoots)
    private val seen = HashSet<Id>()
    private val nfhashTable: BiMap<Hash, SNode> = HashBiMap.create()
    // invariant: nodes in the hash table are in normal form
    private val LOG = LogFactory.getLog(SPlanEnumerate::class.java)!!

    fun expandAll() {
        while( remainingToExpand.isNotEmpty() )
            expand()
    }

    private fun expand() {
        expand(remainingToExpand.removeFirst() ?: return)
    }

    private fun expand(node: SNode) {
        if( node.id in seen ) // todo replace with visit flag
            return
        seen += node.id

        // todo - start bottom up? Then we recgonize when we have a sub-normal form?
        // go through algorithm with +, Σ, *

        when( node ) {
            is SNodeData -> return node.inputs.forEach { expand(it) }
            is SNodeExt -> return node.inputs.forEach { expand(it) }
            is SNodeUnbind -> return expand(node.input)
            is SNodeBind -> return expand(node.input)
            is OrNode -> return // OrNodes are already expanded.
            is ENode -> throw AssertionError("unexpected ENode")
        }

        // node is SNodeNary or SNodeAggregate in normal form. Check if a semantically equivalent node is in hash table.
        val nn = addToHashTable(node)
        if( nn === node ) { // node was not in the hash table; we need to explore it
            when (node) {
                is SNodeNary -> expandNary(node)
                is SNodeAggregate -> expandAggregate(node)
            }
        }
    }

    private fun expandNary(nary: SNodeNary) {
        if (nary.op == SNodeNary.NaryOp.MULT) {
            // Multiply within groups. If there are more than 2 inputs, see if we can group them into sub-*s.
            if (nary.inputs.size > 2) {
                val edgesGroupByIncidentNames = groupByIncidentNames(nary)
                edgesGroupByIncidentNames.forEach { (_, edges) ->
                    if (edges.size > 1) { // multiply within group
                        /*       *     =>   *
                               A B A       B *
                                            A A
                         */
                        pushDownMultiplyGroup(nary, edges)
                    }
                }
                // todo still more than 2 inputs? Somehow break these up into binary *s. Possibly use an OrNode
                // todo change self-multiply to power?
            }
            return nary.inputs.forEach { expand(it) }
        }
        else if (nary.op == SNodeNary.NaryOp.PLUS) {
            // todo PLUS
            return nary.inputs.forEach { expand(it) }
        }
    }

    private fun expandAggregate(agg: SNodeAggregate) {
        // already checked the hash table for the aggregate.
        // invariant: Σ-*-ext
        assert(agg.aggsNotInInputSchema().isEmpty()) {"(${agg.id}) $agg aggs not in input schema: ${agg.aggsNotInInputSchema()}"}

        if( agg.op == Hop.AggOp.SUM && agg.input is SNodeNary && (agg.input as SNodeNary).op == SNodeNary.NaryOp.MULT ) {
            // First do simple rewrites:
            // 0. Split the * away in order to not affect foreign parents on *. Todo: only do this if we are going to change the * in some way.
            val mult = if (agg.input.parents.all { it == agg }) agg.input as SNodeNary else SPlan2NormalForm_InsertStyle.splitCse(agg, agg.input as SNodeNary)

            // 1. Partition aggNames by connected components. Factor edges into a sub-multiply for each partition.
            // two aggNames are connected if there is an edge that contains both aggNames in its schema.
            // If an aggName can be factored into a subset of mult's inputs, do it.
            // Non-aggregated inputs have their own component.
            val CCs = findConnectedAggs(agg, mult) // todo unnecessary if parent of agg is *
            if (CCs.size >= 2) {
                for ((_, Cedges) in CCs) {
                    if (Cedges.size >= 2)
                        pushDownMultiplyGroup(mult, Cedges)
                }
                pushAggregations(agg, mult)
                // we should have pushed all the aggregations
                assert(agg.aggs.isEmpty())
                eliminateNode(agg)
                // change hash table entry to mult.
                val hash = nfhashTable.inverse().remove(agg)!!
                nfhashTable[hash] = mult
                // continue to each partition
                return mult.inputs.forEach { expand(it) }
            }

            // Stop if there is a single aggName or there is a single edge group.
            if (agg.aggs.size == 1)
                return expand(mult)
            val edgesGroupByIncidentNames = groupByIncidentNames(mult)
            if( edgesGroupByIncidentNames.size == 1 )
                return expand(mult)

            // 3. Identify easy aggregates. Easy aggNames are those that are contained within one edge and can be pushed into a sub-Σ-* edge group.
            // Not all degree 1 aggregates are easy, as in t(u)Av.
            val easyAggs = anticipatePushableAggs(agg, mult)

            if (easyAggs != agg.aggs.names) {
                // we have at least one hard aggregate. We have a choice over the hard aggregates of which one to leave up top.
                @Suppress("UNCHECKED_CAST")
                val hardAggs = (agg.aggs.names - easyAggs) as Set<AB>
                if (hardAggs.size >= 2) {
                    // todo max degree heuristic
                    // Replace agg with an OrNode - we have choices.
                    val orNode = replaceWithOrNode(agg)
                    agg.parents.clear()   // use agg as master copy
                    orNode.inputs.clear()

                    // todo - heuristics for ordering which to explore first (order hardAggs)

                    for (hardAgg in hardAggs) {
                        val curMult = mult.shallowCopyNoParentsYesInputs()
                        val curAgg = agg.shallowCopy(curMult)
                        curAgg.aggs -= hardAgg
                        curAgg.refreshSchema()
                        val curAggHard = SNodeAggregate(Hop.AggOp.SUM, curAgg, hardAgg)
                        // curAggHard has same hash as orNode.
                        curAggHard.parents += orNode
                        orNode.inputs += curAggHard
                        expand(curAgg)

                        // todo - costing/pruning in the middle of enumeration
                        // (decide whether to kill a child of the orNode by removing its parent and stripDead())
                    }
                    // eliminate master copy
                    stripDead(agg)
                    return
                } else {
                    // just one hard agg. No OrNode necessary.
                    val hardAgg = hardAggs.single()
                    mult.parents -= agg
                    agg.aggs -= hardAgg
                    val midAgg = SNodeAggregate(Hop.AggOp.SUM, mult, hardAgg)
                    agg.input = midAgg
                    midAgg.parents += agg
                    expand(midAgg)
                    return
                }
            } else {
                // All easy aggregates.
                // we're finished, aren't we?
                throw SNodeException(agg, "easy aggregates remain?")
            }


        }
    }

    private fun findConnectedAggs(agg: SNodeAggregate, mult: SNodeNary): Set<Pair<Set<AB>, List<SNode>>> {
        val aggsRemaining = agg.aggs.names.toMutableSet()
        val ret = mutableSetOf<Pair<Set<AB>, List<SNode>>>()
        val edges = mult.inputs.toMutableList()
        while (aggsRemaining.isNotEmpty()) {
            val a = aggsRemaining.first() as AB
            val component = findConnectedAggs(agg.aggs.names, a, edges)
            aggsRemaining -= component.first
            ret += component
        }
        if (edges.isNotEmpty())
            ret += setOf<AB>() to edges // no-aggregate edges
        return ret
    }

    /**
     * Find all inputs to [edges] that are in the same connected component as [aggName].
     * An input is in the same connected component as [aggName] if it has a name of the same connected component as [aggName] in its schema.
     * Two names are connected if an input to [edges] contains both in its schema.
     * Return the names and input in the connected component.
     *
     * Modifies [edges]: deletes found edges.
     */
    @Suppress("UNCHECKED_CAST")
    private fun findConnectedAggs(allAggs: Set<Name>, aggName: AB, edges: MutableList<SNode>): Pair<Set<AB>, List<SNode>> {
        val connectedNodes = mutableListOf<SNode>()
        var toExplore = setOf(aggName)
        val explored = mutableSetOf<AB>()
        do {
            val found = edges.filter { !toExplore.disjoint(it.schema.names) }
            edges.removeAll(found)
            connectedNodes += found
            explored += toExplore
            toExplore = found.flatMap { it.schema.names.intersect(allAggs) as Set<AB> }.toSet() - explored
        } while (toExplore.isNotEmpty())
        return explored to connectedNodes
    }

    /**
     * Push a group of multiplicands into a new sub-multiply.
     * Return the new sub-multiply.
     */
    private fun pushDownMultiplyGroup(mult: SNodeNary, factorEdges: List<SNode>): SNodeNary {
        mult.inputs.removeAll(factorEdges)
        factorEdges.forEach { it.parents -= mult }
        val nm = SNodeNary(SNodeNary.NaryOp.MULT, factorEdges)
        mult.inputs += nm
        nm.parents += mult
        return nm
    }

    private fun anticipatePushableAggs(agg: SNodeAggregate, mult: SNodeNary): Set<AB> {
        assert(agg.input == mult)
        val pushable = mutableSetOf<AB>()
        for ((aggName, _) in agg.aggs) {
            aggName as AB
            val incidentEdges = mult.inputs.filter { aggName in it.schema } //nameToIncidentEdges(mult)[aggName]!!
            val e = incidentEdges[0]
            if (incidentEdges.subList(1,incidentEdges.size).all { it.schema == e.schema })
                pushable += aggName
        }
        return pushable
    }

    /**
     * Input: [agg]-[mult].
     * For each aggregated index, check if it can be pushed down into a single input of [mult].
     * Push down each one that can.
     */
    private fun pushAggregations(agg: SNodeAggregate, mult: SNodeNary) {
        assert(agg.input == mult)
        val iter = agg.aggs.iterator()
        while (iter.hasNext()) {
            val (aggName, aggShape) = iter.next()
            aggName as AB
            val incidentEdges = mult.inputs.filter { aggName in it.schema } //nameToIncidentEdges(mult)[aggName]!!
            if (incidentEdges.size == 1) {
                val single = incidentEdges[0]
                // from Σ -> * -> *
                // to   Σ -> * -> Σ -> *
                // [mult] changes semantics.
                iter.remove()
                if (single is SNodeAggregate && single.op == Hop.AggOp.SUM) {
                    single.aggs.put(aggName, aggShape)
                    single.refreshSchema()
                } else {
                    single.parents -= mult
                    val nagg = SNodeAggregate(Hop.AggOp.SUM, single, aggName)
                    mult.inputs[mult.inputs.indexOf(single)] = nagg
                    nagg.parents += mult
                }
                mult.refreshSchema()
            }
        }
    }

    /**
     * If [node] has a semantically equivalent sister inside the hash table,
     * then rewire [node]'s parents to its sister and return the sister.
     * Otherwise add [node] to the hash table and return itself.
     */
    private fun addToHashTable(node: SNode): SNode {
        val hash = NormalFormHash.hashNormalForm(node)
        return if( hash in nfhashTable ) {
            val collisionNode = nfhashTable[hash]!!
            if( collisionNode === node )
                throw AssertionError("should not visit same node twice")
            // wire to existing enumerated normal form
            moveParentsToEquivalentNode(node, collisionNode)
            collisionNode
        } else {
            nfhashTable[hash] = node
            node
        }
    }

    private fun nameToAdjacentNames(mult: SNodeNary): Map<Name, Set<Name>> {
        return nameToIncidentEdges(mult).mapValues { (_,edges) ->
            edges.flatMap { it.schema.names }.toSet()
        }
    }

    private fun groupByIncidentNames(mult: SNodeNary): Map<Set<Name>, List<SNode>> {
        return mult.inputs.groupBy { it.schema.names.toSet() }
    }

    private fun nameToIncidentEdges(mult: SNodeNary): Map<Name, List<SNode>> {
        return mult.inputs.flatMap { edge ->
            edge.schema.names.map { name -> name to edge }
        }.groupBy(Pair<Name, SNode>::first)
                .mapValues { (n,v) ->
                    v.map(Pair<Name, SNode>::second)
                            // matrix[x,n], vector [n], matrix[n,x]
                            .sortedBy {
                                when( it.schema.size ) {
                                    0 -> 0
                                    1 -> 2
                                    else -> if( it.schema.names.first() == n ) 3 else 1
                                }
                            }
                }
    }

    /** Replace [node] with an [OrNode], having [node] as its only child. Move parents of [node] to the [OrNode].
     *  If [node] is in [nfhashTable], move its hash table entry to the OrNode. */
    private fun replaceWithOrNode(node: SNode): OrNode {
        return if( node !is OrNode ) {
            val parents = ArrayList(node.parents)
            node.parents.clear()
            val orNode = OrNode(node)
            parents.forEach {
                it.inputs[it.inputs.indexOf(node)] = orNode
            }
            orNode.parents += parents

            val hash = nfhashTable.inverse().remove(node)
            if (hash != null)
                nfhashTable[hash] = orNode
            orNode
        } else node
    }

    /**
     * Move parents of [node] to [collisionNode], with an unbind/bind in between the [collisionNode] and [node]'s parents if necessary.
     * Strips away [node] as it is now dead code.
     */
    private fun moveParentsToEquivalentNode(node: SNode, collisionNode: SNode) {
        // move node's parents to collision node, after rebinding to schema of node
        val parents = ArrayList(node.parents)
        node.parents.clear()

        val aboveCollision = if( node.schema != collisionNode.schema ) {
            // need to map node's names to orNode's names
            val nodePosList = NormalFormHash.createAttributePositionList(node)
            val orPosList = NormalFormHash.createAttributePositionList(collisionNode)

            val unbindMapping = mutableMapOf<AU,AB>()
            val bindMapping = mutableMapOf<AU,AB>()
            collisionNode.schema.names.fold(AU.U0) { acc, mn ->
                val pos = orPosList.indexOf(mn)
                val nn = nodePosList[pos]
                if( mn == nn ) acc
                else {
                    unbindMapping.put(acc, mn as AB)
                    bindMapping.put(acc, nn)
                    AU(acc.dim + 1)
                }
            }
            // small optimization: if single parent and it is an SNodeUnbind, then do unbind-bind elimination
            if( parents.size == 1 && parents[0] is SNodeUnbind ) {
                val unbindAbove = parents[0] as SNodeUnbind
                unbindAbove.unbindings.intersectEntries(bindMapping).forEach { au, _ ->
                    bindMapping -= au
                    unbindAbove.unbindings -= au
                }
                if( unbindAbove.unbindings.isEmpty() ) {
                    parents.clear()
                    parents += unbindAbove.parents
                    parents.forEach {
                        it.inputs[it.inputs.indexOf(unbindAbove)] = node
                    }
                }
            }
            when {
                unbindMapping.isEmpty() -> collisionNode
                bindMapping.isEmpty() -> SNodeUnbind(collisionNode, unbindMapping)
                else -> SNodeBind(SNodeUnbind(collisionNode, unbindMapping), bindMapping)
            }
        } else collisionNode

        parents.forEach {
            it.inputs[it.inputs.indexOf(node)] = aboveCollision
        }
        aboveCollision.parents += parents

        // eliminate node
        stripDead(node)
    }
}
package org.apache.sysml.hops.spoof2.enu2

import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.spoof2.NormalFormHash
import org.apache.sysml.hops.spoof2.enu.ENode
import org.apache.sysml.hops.spoof2.plan.*

class SPlanEnumerate(initialRoots: Collection<SNode>) {

    constructor(vararg inputs: SNode) : this(inputs.asList())

    // todo - configuration parameters for whether to expand +, prune, etc.
    private val remainingToExpand = HashSet(initialRoots)
    private val seen = HashSet<Id>()
    private val nfhashTable = HashMap<Hash, SNode>()
    // invariant: nodes in the hash table are in normal form

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
            is OrNode -> return
            is ENode -> throw AssertionError("unexpected ENode")
        }

        // node is SNodeNary or SNodeAggregate in normal form
        val nn = addToHashTable(node)
        if( nn === node ) { // node was not in the hash table; we need to explore it
            when (node) {
                is SNodeNary -> expandNary(node)
                is SNodeAggregate -> expandAggregate(node)
            }
            node.inputs.forEach { expand(it) }
        }
    }

    private fun expandNary(nary: SNodeNary) {
        TODO("not implemented")
    }

    private fun expandAggregate(agg: SNodeAggregate) {
        assert(agg.aggsNotInInputSchema().isNotEmpty()) {"(${agg.id}) $agg aggs not in input schema: ${agg.aggsNotInInputSchema()}"}
        val mult = agg.input
        if( agg.op == Hop.AggOp.SUM && mult is SNodeNary && mult.op == SNodeNary.NaryOp.MULT ) {
            // decision: order in which to push down Σ into *
            // Are there decisions at all? Yes: copy original and make decisions underneath an OrNode.
            // Otherwise nothing to expand; skip past this agg-multiply.

            // todo wait-- do simple factorization first -- multiply within groups, separate into connected components, push down independent aggregates
            val edgesGroupByIncidentNames = groupByIncidentNames(mult)
            if( edgesGroupByIncidentNames.size == 1 )
                return
            edgesGroupByIncidentNames.forEach { _, edges ->
                if (edges.size > 1) { // multiply within group
                    /*       *     =>   *
                           A B A       B *   <-- New nf
                                        A A

                             Σ          Σ
                             *     =>   *    <-- New nf
                           A B A       B Σ   <-- New nf
                                         *   <-- New nf
                                        A A
                     */
                    pushDownMultiplyGroup(agg, mult, edges)
                }
            }
            pushAggregations(agg)


            if (isSimpleAggMultiply(agg, mult)) {
                return expand(mult)
            }
            // copy original, hold onto it
            // create an OrNode, move parents of agg onto the OrNode
            // for each factorization, add it to the OrNode's input.
            // check for existing nfhash along the way.
            //    If one is found, stop factorizing and link to the existing semantically equivalent node.
            // dead code eliminate the original.
            // add the leaves to the frontier. Leaves are the original mult's inputs.


        }
    }

    private fun isSimpleAggMultiply(agg: SNodeAggregate, mult: SNodeNary): Boolean {
        return agg.aggs.size == 1
    }

    /**
     * Push a group of multiplicands into a new sub-multiply.
     * Factor down Σs that are restricted to them.
     *
     * Does not change semantics of agg.
     * Possibly changes semantics of mult.
     */
    private fun pushDownMultiplyGroup(agg: SNodeAggregate, mult: SNodeNary, factorEdges: List<SNode>) {
        mult.inputs.removeAll(factorEdges)
        factorEdges.forEach { it.parents -= mult }
        var nm: SNode = SNodeNary(SNodeNary.NaryOp.MULT, factorEdges)
        mult.inputs += nm
        nm.parents += mult
        // new nf. It is in normal form.
        nm = addToHashTable(nm)
//        pushAggregations(agg, mult)
    }

    private fun pushAggregations(agg: SNodeAggregate, mult: SNodeNary) {
        assert(agg.input == mult)
        val iter = agg.aggs.iterator()
        while (iter.hasNext()) {
            val (aggName, shape) = iter.next()
            aggName as AB
            val incidentEdges = nameToIncidentEdges(mult)[aggName]!!
            if (incidentEdges.size == 1) {
                val bmult = incidentEdges[0]
                // from Σ -> * -> *
                // to   Σ -> * -> Σ -> *
                // [mult] changes semantics.
                iter.remove()
                bmult.parents -= mult
                val nagg = SNodeAggregate(Hop.AggOp.SUM, bmult, aggName)
                mult.inputs[mult.inputs.indexOf(bmult)] = nagg
                mult.refreshSchema()
                // new Σ is ready to be inserted
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

    /** Replace [node] with an [OrNode], having [node] as its only child. Move parents of [node] to the [OrNode]. */
    private fun replaceWithOrNode(node: SNode): OrNode {
        return if( node !is OrNode ) {
            val parents = ArrayList(node.parents)
            node.parents.clear()
            val orNode = OrNode(node)
            parents.forEach {
                it.inputs[it.inputs.indexOf(node)] = orNode
            }
            orNode.parents += parents
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
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

        when( node ) {
            is SNodeData -> return node.inputs.forEach { expand(it) }
            is SNodeExt -> return node.inputs.forEach { expand(it) }
            is SNodeUnbind -> return expand(node.input)
            is SNodeBind -> return expand(node.input)
            is OrNode -> return
            is ENode -> throw AssertionError("unexpected ENode")
        }

        // node is SNodeNary or SNodeAggregate in normal form
        val hash = NormalFormHash.hashNormalForm(node)
        if( hash in nfhashTable ) {
            val collisionNode = nfhashTable[hash]!!
            if( collisionNode === node )
                throw AssertionError("should not visit same node twice")
            // wire to existing enumerated normal form
            moveParentsToEquivalentNode(node, collisionNode)
            return
        } else {
            nfhashTable[hash] = node
            when (node) {
                is SNodeNary -> expandNary(node)
                is SNodeAggregate -> expandAggregate(node)
            }
            return node.inputs.forEach { expand(it) }
        }
    }

    private fun expandNary(nary: SNodeNary) {
        TODO("not implemented")
    }

    private fun expandAggregate(agg: SNodeAggregate) {
        val mult = agg.input
        if( agg.op == Hop.AggOp.SUM && mult is SNodeNary && mult.op == SNodeNary.NaryOp.MULT ) {
            // decision: order in which to push down Σ into *
            // Are there decisions at all? Yes: copy original and make decisions underneath an OrNode.
            // Otherwise nothing to expand; skip past this agg-multiply.

            // todo wait-- do simple factorization first -- multiply within groups, separate into connected components, push down independent aggregates


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
                    factorDownEdges(agg, mult, edges)
                }
            }
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
    private fun factorDownEdges(agg: SNodeAggregate, mult: SNodeNary, factorEdges: List<SNode>) {
        mult.inputs.removeAll(factorEdges)
        factorEdges.forEach { it.parents -= mult }
        val nm = SNodeNary(SNodeNary.NaryOp.MULT, factorEdges)
        mult.inputs += nm
        nm.parents += mult
        // new nf: mult
        // pushAggregations(agg, mult)
    }

    private fun groupByIncidentNames(mult: SNodeNary): Map<Set<Name>, List<SNode>> {
        return mult.inputs.groupBy { it.schema.names.toSet() }
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
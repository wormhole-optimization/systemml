package org.apache.sysml.hops.spoof2

import org.apache.sysml.hops.spoof2.enu.ENode
import org.apache.sysml.hops.spoof2.plan.*

object NormalFormHash {

    fun createAttributePositionList(node: SNode, memo: MutableMap<Id, List<AB>>): List<AB> {
        if( node.id in memo )
            return memo[node.id]!!

        val map: List<AB> = when (node) {
            is SNodeData -> listOf()
            is SNodeBind -> { check(createAttributePositionList(node.input, memo).isEmpty()) { "there should be no bindings underneath SNodeBind (normal form should have one layer of binds)" }
                check(node.bindings.keys.map { it.dim }.sorted() == (0 until node.bindings.size).toList()) { "the bound dimensions should be the contiguous natural numbers 1 upto a number N" }
                node.bindings.entries.sortedBy { it.key.dim }.map { it.value }
            }
            is SNodeNary -> {
                node.inputs.fold(listOf()) { acc, input ->
                    val inputList = createAttributePositionList(input, memo)
                    acc + inputList.filter { it !in acc }
                }
            }
            is SNodeAggregate -> node.aggs.names.fold(createAttributePositionList(node.input, memo)) { acc, aggName ->
                acc - aggName as AB
            }
            is SNodeUnbind -> {
                check(createAttributePositionList(node.input, memo).toSet() == node.unbindings.values) {"there are more attributes present in the input to this SNodeUnbind than are in the unbindings"}
                listOf()
            }
            is SNodeExt -> {
                node.inputs.forEach { check(createAttributePositionList(it, memo).isEmpty()) {"An SNodeExt should not have bound attributes from its inputs"} }
                listOf()
            }
            is ENode -> throw IllegalStateException("There should not be an ENode present during createAttributePositionList")
            else -> throw IllegalStateException("Unrecognized: $node")
        }
        
        memo[node.id] = map
        return map
    }

    /**
     * Compute a hash value for this SPlan tree, assuming that it is in normal form.
     * The hash value can be used to compare SPlan trees in normal form for semantic equivalence.
     */
    fun hashNormalForm(node: SNode): Hash {
        return hashNormalForm(node, mutableMapOf(), mutableMapOf())
    }

    fun hashNormalForm(node: SNode, memo: MutableMap<Id, Hash>, attrPosMemo: MutableMap<Id, List<AB>>): Hash {
        if( node.id in memo )
            return memo[node.id]!!
        val inputsHashes = node.inputs.map { hashNormalForm(it, memo, attrPosMemo) }

        val h = when (node) {
            is SNodeData -> (node.hop.opString + inputsHashes.joinToString(prefix = " (", postfix = ")", separator = "_", transform = Int::toString)).hashCode()
            is SNodeExt -> (node.hop.opString + inputsHashes.joinToString(prefix = " (", postfix = ")", separator = "_", transform = Int::toString)).hashCode()
            is SNodeBind -> inputsHashes[0]
            is SNodeUnbind -> inputsHashes[0]
            is SNodeAggregate -> {
                val inputAttributePositions = createAttributePositionList(node.input, attrPosMemo)
                val aggPos = node.aggs.names.map { inputAttributePositions.indexOf(it) }.sorted()
                "${node.op}$aggPos(${inputsHashes[0]})".hashCode()
            }
            is SNodeNary -> {
                // 0. Get the positions of the attributes in the inputs
                var inputAttributePositions = node.inputs.map { createAttributePositionList(it, attrPosMemo) }
                // 0. Get the hashes of the inputs.
                val inputHashMap = node.inputs.zip(inputsHashes).toMap()

                if( node.op.commutative ) {
                    // 1. Separate the inputs into connected components.
                    val CCs = partitionInputsByJoinConditions(node.inputs)
                    // 2. Create a join string used for ordering in steps 3 and 4.
                    val joinConditions = getJoinConditions(node.inputs, inputAttributePositions)
                    // 3. Order across connected components.
                    val CCsSorted = CCs.map { CC ->
                        val CCjoinConditions = joinConditions.filter { !CC.disjoint(it.nodesPresent) }

                        // 4. Order within connected components.
                        val CCsortedWithHashAndPos =
                                CC.map { n ->
                                    val h = inputHashMap[n]!!
                                    val x = joinConditionsToSortedString(CCjoinConditions.filter { n in it.nodesPresent }, inputHashMap)
                                    n to (h to x.hashCode())
                                }.sortedWith(secondPairComparator())

                        val CCsortedNodeHashString = CCsortedWithHashAndPos.joinToString(separator = "_") { (_,pair) ->
                            pair.first.toString()
                        }
                        val joinHashString = joinConditionsToSortedString(CCjoinConditions, inputHashMap)
                        val hashString = CCsortedNodeHashString + "~~" + joinHashString
                        val CCsorted = CCsortedWithHashAndPos.map { it.first }
                        CCsorted to hashString.hashCode()
                    }.sortedBy { it.second }.map { it.first }
                    // Further ties should indicate exact equality

                    val fullySortedOrder = CCsSorted.flatten()
                    if( fullySortedOrder != node.inputs ) { // we changed the order of inputs
                        inputAttributePositions = fullySortedOrder.map { createAttributePositionList(it, attrPosMemo) }
                    }
                    node.inputs.clear()
                    node.inputs += fullySortedOrder
                } else {
                    // not commutative; fixed order of inputs
                }
                val joinHashString = joinConditionsToSortedString(getJoinConditions(node.inputs, inputAttributePositions), inputHashMap)
                node.inputs.joinToString(prefix = "${node.op} (", postfix = ")", separator = "_") { inputHashMap[it]!!.toString() }
                        .plus("~~")
                        .plus(joinHashString)
//                        .also { println(it) }
                        .hashCode()
            }
            is ENode -> throw IllegalStateException("There should not be an ENode present during hashNormalForm")
            else -> throw IllegalStateException("Unrecognized: $node")
        }
//        println("(${node.id}) $node ==> $h")
        memo[node.id] = h
        return h
    }

    private fun <A : Comparable<A>, B : Comparable<B>> pairComparator(): Comparator<Pair<A,B>> {
        return Comparator.comparing<Pair<A,B>,A> { it.first }.thenComparing<B> { it.second }
    }
    private fun <T, A : Comparable<A>, B : Comparable<B>> secondPairComparator(): Comparator<Pair<T,Pair<A,B>>> {
        return Comparator.comparing<Pair<T,Pair<A,B>>,A> { it.second.first }.thenComparing<B> { it.second.second }
    }
    private fun joinConditionsToSortedString(jcs: List<JoinCondition>, inputHashes: Map<SNode, Hash>): String {
        return jcs.map { jc ->
            jc.inputsWithPosition.map { (n,p) -> inputHashes[n]!! to p }
                    .sortedWith(pairComparator())
//                    .also{println(it)}
                    .joinToString(separator = "=") { (h,p) -> "$h-$p" }
        }.joinToString(separator = "|")
    }

    private data class JoinCondition(
            val attribute: AB,
            val inputsWithPosition: List<Pair<SNode, Int>>
    ) {
        val nodesPresent: Set<SNode> = inputsWithPosition.map { (n, _) -> n }.toSet()
    }

    private fun getJoinConditions(inputs: List<SNode>, inputAttributePositions: List<List<AB>>): List<JoinCondition> {
        val nameToInput = inputs
                .zip(inputAttributePositions)
                .flatMap { (input, positions) -> input.schema.names.map { it as AB to (input to positions) } }
                .groupBy { it.first }
                .filterValues { it.size > 1 }
                .mapValues { it.value.map { it.second } }
        return nameToInput.map { (n,incidentNodesAndPositions) ->
            val nodesWithJoinPosition = incidentNodesAndPositions.map { (incidentNode, positions) ->
                incidentNode to positions.indexOf(n)
            }
            JoinCondition(n, nodesWithJoinPosition)
        }
    }

    /**
     * Partition the inputs of an SNodeNary into connected components,
     * wherein two inputs are in the same component if the overlap in at least one name.
     */
    private fun partitionInputsByJoinConditions(_inputs: List<SNode>): List<List<SNode>> {
        val components: MutableList<List<SNode>> = mutableListOf()
        val remaining = _inputs.toMutableList()
        while (remaining.isNotEmpty()) {
            components += extractOneComponentByJoinConditions(remaining)
        }
        return components
    }

    /**
     * Extracts one connected component from [remaining] (modifying it in place) and returns the component.
     * Assumes that [remaining] is not empty.
     */
    @Suppress("UNCHECKED_CAST")
    private fun extractOneComponentByJoinConditions(remaining: MutableList<SNode>): List<SNode> {
        val component = mutableListOf<SNode>()
        component.add(remaining.removeAt(0))
        val componentAttributes = mutableSetOf<AB>()
        componentAttributes += component[0].schema.names as Set<AB>
        do {
            val modify = remaining.filterInPlace {
                if( !it.schema.names.disjoint(componentAttributes) ) {
                    component += it
                    componentAttributes += it.schema.names as Set<AB>
                    false
                } else true
            }
        } while (modify)
        return component
    }

}
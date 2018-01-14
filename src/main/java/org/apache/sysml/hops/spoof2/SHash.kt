package org.apache.sysml.hops.spoof2

import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.spoof2.enu.ENode
import org.apache.sysml.hops.spoof2.enu2.OrNode
import org.apache.sysml.hops.spoof2.plan.*

private typealias InputIdx = Int
private typealias AttrPosition = Int

object SHash {

    fun createAttributePositionList(node: SNode, memo: MutableMap<Id, List<AB>> = mutableMapOf()): List<AB> {
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
            is OrNode -> createAttributePositionList(node.inputs[0], memo)
            is ENode -> throw IllegalStateException("There should not be an ENode present during createAttributePositionList")
            else -> throw IllegalStateException("Unrecognized: $node")
        }

//        println("attrPosList (${node.id}) $node: $map")
        memo[node.id] = map
        return map
    }

    fun prettyPrintByPosition(node: SNode): String {
        return prettyPrintByPosition(node, mutableMapOf(), mutableMapOf())
    }

    fun prettyPrintByPosition(node: SNode, memo: MutableMap<Id, String>, attrPosMemo: MutableMap<Id, List<AB>>): String {
        if( node.id in memo )
            return memo[node.id]!!
        if( node is OrNode )
            return prettyPrintByPosition(node.inputs[0], memo, attrPosMemo)
        var inputsHashes = node.inputs.map { prettyPrintByPosition(it, memo, attrPosMemo) }

        val h = when (node) {
            is SNodeData -> node.hop.opString + inputsHashes
            is SNodeExt -> node.hop.opString + inputsHashes
            is SNodeBind -> inputsHashes[0]
            is SNodeUnbind -> inputsHashes[0]
            is SNodeAggregate -> {
                val inputAttributePositions = createAttributePositionList(node.input, attrPosMemo)
                val aggPos = node.aggs.names.map { inputAttributePositions.indexOf(it) }.sorted()
                "${node.op}${aggPos.joinToString(",", "[", "]")}(${inputsHashes[0]})"
            }
            is SNodeNary -> {
                var inputAttributePositions = node.inputs.map { createAttributePositionList(it, attrPosMemo) }

                if( node.op.commutative && node.inputs.size > 1 ) {
                    val changed = normalizeCommutativeNaryInputOrder(node, inputsHashes, inputAttributePositions)
                    if( changed ) {
                        inputsHashes = node.inputs.map { prettyPrintByPosition(it, memo, attrPosMemo) }
                        inputAttributePositions = node.inputs.map { createAttributePositionList(it, attrPosMemo) }
                    }
                } // otherwise not commutative or trivial; fixed order of inputs

                val body = naryInputsToString(node.inputs, inputsHashes, inputAttributePositions)
                return "${node.op}($body)"
            }
            is ENode -> throw IllegalStateException("There should not be an ENode present during canonize")
            else -> throw IllegalStateException("Unrecognized: $node")
        }
//        println("(${node.id}) $node ==> $h")
        memo[node.id] = h
        return h
    }

    private fun normalizeCommutativeNaryInputOrder(node: SNodeNary, inputHashStrings: List<String>, inputAttributePositions: List<List<AB>>): Boolean {
        // 1. Separate the inputs into connected components.
        val CCs = partitionInputIndicesByJoinConditions(node.inputs)
        // 2. Create a join string used for ordering in steps 3 and 4.
        val joinConditions = getJoinConditions(node.inputs, inputAttributePositions)
        // 3. Order across connected components.
        val CCsSorted = CCs.map { CC ->
            // 4. Order within connected components.
            // 4a. Sort by node hash string.
            // 4b. Of those non-identical inputs that 4a does not distinguish,
            //      sort by join condition string, referring to the node hash strings.
            // 4c. Of those inputs that 4b does not distinguish,
            //      enumerate all combinations and select the lexicographically least.
            val sortA: (Int) -> String = inputHashStrings::get
            val sortB: (Int) -> String = { iidx ->
                val input = node.inputs[iidx]
                val overlapJc = joinConditions.filter { iidx in it.inputIdxPresent }
                input.schema.names.joinToString(",", "[", "]") { name ->
                    overlapJc.find { it.attribute == name }
                            ?.toStringReferenceName(inputHashStrings, iidx)
                            ?: ""
                }
            }
            val CCsorted = sortIndicesHierarchical(CC, listOf(sortA, sortB))
            // todo - further ties that are not exact equality are possible, as in symmetrical expressions like (AB)^T(AB)
            CCsorted
        }.sortedBy { CC ->
            // Create hash string for this CC
            val nodeStr = CC.joinToString(",", "[", "]") { inputHashStrings[it] }
            val jcInCC = joinConditions.filter { !CC.disjoint(it.inputIdxPresent) }
            val jcStr = jcInCC.joinToString(",", "[", "]") { it.toStringReferenceIndex() }
            "$nodeStr~$jcStr"
        }

        val fullySortedOrder = CCsSorted.flatten()
        return if( fullySortedOrder != node.inputs.indices.toList() ) { // we changed the order of inputs
            val newInputs = node.inputs.permute(fullySortedOrder)
            node.inputs.clear()
            node.inputs += newInputs
            true
        } else false
    }

    private fun naryInputsToString(inputs: List<SNode>, inputStrings: List<String>, inputAttributePositions: List<List<AB>>): String {
        val CCs = partitionInputIndicesByJoinConditions(inputs)
        val joinConditions = getJoinConditions(inputs, inputAttributePositions)
        return CCs.joinToString("|") { CC -> naryInputCCToString(inputStrings, joinConditions.filter { !CC.disjoint(it.inputIdxPresent) }) }
    }

    private fun naryInputCCToString(nodeStrings: List<String>, jcInCC: List<JoinCondition>): String {
        val nodeStr = nodeStrings.joinToString(",", "[", "]")
        val jcStr = jcInCC.joinToString(",", "[", "]") { it.toStringReferenceIndex() }
        return "$nodeStr~$jcStr"
    }


//    fun hash(B0: GraphBag, memo: CanonMemo): Hash {
//        if( B0 in memo ) return memo[B0]
//        var B = B0
//        var inputsHashes = B.map { hash(it, memo) }
//        // return a new GraphBag (list) with the canonical order.
//
//        if( inputsHashes.size > 1 ) {
//            val perm = normalizeCommutativeNaryInputOrder(B, inputsHashes)
//            if( perm != 0 until B.size ) {
//                B = B.permute(perm)
//                inputsHashes = inputsHashes.permute(perm)
//            }
//        }
//
//        val body = naryInputsToString(B, inputsHashes)
//        val h = "+($body)"
//
////        println("(${node.id}) $node ==> $h")
//        memo[B] = h
//        return h
//    }



    /**
     * Compute the sort indices of data by sorting with the provided sort functions.
     * Used the each sort function after the first to break ties made by the previous sort function.
     *
     * @param stillConfused An output variable appended with the ranges of positions in the returned array that the [sortFuns] failed to distinguish.
     *                      Sorts!
     * @param returnPerm An output list filled with the permutation found by sorting.
     * @param permCi Confusion indices to sort. Defaults to all the indices.
     * @return [returnPerm]
     */
    fun <T, C: Comparable<C>> sortIndicesHierarchical(
            data: List<T>, sortFuns: List<(T) -> C>, stillConfused: MutableList<IntSlice>? = null,
            returnPerm: MutableList<Int>? = null, permCi: List<Int>? = null): List<Int> {
        if (returnPerm != null) require(returnPerm.size == data.size)
//        if (permCi != null) require(permCi.size == data.size)
        // Turns out there is a standard implementation of this method.
//        if( sortFuns.isEmpty() )
//            return data.indices.toList()
//        val sf0 = sortFuns[0]
//        val c = sortFuns.drop(1).fold(Comparator.comparing<T,C>(sf0)) { acc, sf ->
//            acc.thenComparing<C>(sf)
//        }
//        val f = java.util.function.Function(IndexedValue<T>::value)
//        return data.withIndex().sortedWith(Comparator.comparing<IndexedValue<T>,T>(f, c)).map(IndexedValue<T>::index)

        // this is my own implementation, which should be more efficient in that it evaluates the sortFuns no more than necessary
        val ret = returnPerm ?: data.indices.toMutableList()
        if( sortFuns.isEmpty() ) {
            if( stillConfused != null )
                stillConfused += IntSlice(0, data.size-1)
            return ret
        }
        val ci = permCi ?: data.indices.toList() // confusion indices
        rSortIndicesHierarchical(data, sortFuns, ret, ci, stillConfused)
        // TODO check if this is already sorted
        stillConfused?.sort()
        return ret
    }

    /**
     * Used for a slice of array indices, from [first] to [last] inclusive.
     */
    data class IntSlice(val first: Int, val last: Int): Comparable<IntSlice> {
        inline fun <R> map(transform: (Int) -> R): List<R> = (first..last).map(transform)
        inline fun mapSlice(transform: (Int) -> Int): IntSlice = IntSlice(transform(first), transform(last))
        fun toRange() = first..last
        override fun compareTo(other: IntSlice): Int {
            val c = first.compareTo(other.first)
            if (c != 0) return c
            return last.compareTo(other.last)
        }
        operator fun contains(i: Int) = i in first..last
    }

    private fun <T, C : Comparable<C>> rSortIndicesHierarchical(
            data: List<T>, sortFuns: List<(T) -> C>, ret: MutableList<Int>, ci: List<Int>,
            stillConfused: MutableList<IntSlice>?) {
        val dataSub = ci.map { data[ret[it]] }
        val prox = dataSub.map(sortFuns[0])
        val sp = prox.withIndex().sortedBy { it.value }
        val oldRet: List<Int> = ArrayList(ret)
        sp.indices.forEach { i ->
            ret[ci[i]] = oldRet[ci[sp[i].index]]
        }
        val rangesOfSameProx: List<IntSlice> = getRangesOfRepeatedValue(sp.map{it.value})
        val remainingSortFuns = sortFuns.drop(1)
        if( remainingSortFuns.isEmpty() ) {
            if( stillConfused != null )
                stillConfused += rangesOfSameProx.map { it.mapSlice { ci[it] } }
            return
        }
        rangesOfSameProx.forEach { range ->
            val newCi = range.map { ci[it] }
            rSortIndicesHierarchical(data, remainingSortFuns, ret, newCi, stillConfused)
        }
    }

    /**
     * Given a list of items, return the ranges of indices
     * that have the same item, are consecutive, and have length at least 2.
     */
    private fun getRangesOfRepeatedValue(sp: List<Any?>): List<IntSlice> {
        if( sp.size <= 1 )
            return listOf()
        var repVal = sp[0]
        var startIdx = 0
        val ranges = mutableListOf<IntSlice>()
        for (i in 1 until sp.size) {
            if( sp[i] != repVal ) {
                // match on [startIdx, idx-1]
                if( startIdx != i - 1 )
                    ranges += IntSlice(startIdx, i-1)
                repVal = sp[i]
                startIdx = i
            }
        }
        if( startIdx != sp.size - 1 )
            ranges += IntSlice(startIdx, sp.size-1)
        return ranges
    }

    /**
     * Compute a hash value for this SPlan tree, assuming that it is in normal form.
     * The hash value can be used to compare SPlan trees in normal form for semantic equivalence.
     *
     * This method modifies the order of inputs to commutative SNodeNary nodes into a canonical order.
     */
    fun hash(node: SNode): Rep {
        return hash(node, mutableMapOf(), mutableMapOf())
    }

    fun hash(node: SNode, memo: MutableMap<Id, String>, attrPosMemo: MutableMap<Id, List<AB>>): Rep {
        return prettyPrintByPosition(node, memo, attrPosMemo)
/*        if( node.id in memo )
//            return memo[node.id]!!
//        val inputsHashes = node.inputs.map { hash(it, memo, attrPosMemo) }
//
//        val h = when (node) {
//            is SNodeData -> (node.hop.opString + inputsHashes.joinToString(prefix = " (", postfix = ")", separator = "_", transform = Int::toString)).hashCode()
//            is SNodeExt -> (node.hop.opString + inputsHashes.joinToString(prefix = " (", postfix = ")", separator = "_", transform = Int::toString)).hashCode()
//            is SNodeBind -> inputsHashes[0]
//            is SNodeUnbind -> inputsHashes[0]
//            is SNodeAggregate -> {
//                val inputAttributePositions = createAttributePositionList(node.input, attrPosMemo)
//                val aggPos = node.aggs.names.map { inputAttributePositions.indexOf(it) }.sorted()
//                val s = "${node.op}$aggPos(${inputsHashes[0]})"
//                s.hashCode()
//            }
//            is SNodeNary -> {
//                // 0. Get the positions of the attributes in the inputs
//                var inputAttributePositions = node.inputs.map { createAttributePositionList(it, attrPosMemo) }
//                // 0. Get the hashes of the inputs.
//                val inputHashMap = node.inputs.zip(inputsHashes).toMap()
//
//                if( node.op.commutative && node.inputs.size > 1 ) {
//                    // 1. Separate the inputs into connected components.
//                    val CCs = partitionInputsByJoinConditions(node.inputs)
//                    // 2. Create a join string used for ordering in steps 3 and 4.
//                    val joinConditions = getJoinConditions(node.inputs, inputAttributePositions)
//                    // 3. Order across connected components.
//                    val CCsSorted = CCs.map { CC ->
//                        val CCjoinConditions = joinConditions.filter { !CC.disjoint(it.inputIdxPresent) }
//
//                        // 4. Order within connected components.
//                        val CCsortedWithHashAndPos =
//                                CC.map { n ->
//                                    val h = inputHashMap[n]!!
//                                    val x = joinConditionsToSortedString(listOf(n), CCjoinConditions)
//                                    n to (h to x.hashCode())
//                                }.sortedWith(secondPairComparator())
//
//                        val CCsortedNodeHashString = CCsortedWithHashAndPos.joinToString(separator = "_") { (_,pair) ->
//                            pair.first.toString()
//                        }
//                        val joinHashString = joinConditionsToSortedString(CCjoinConditions, inputHashMap)
//                        val hashString = CCsortedNodeHashString + "~~" + joinHashString
//                        val CCsorted = CCsortedWithHashAndPos.map { it.first }
//                        CCsorted to hashString.hashCode()
//                    }.sortedBy { it.second }.map { it.first }
//                    // Further ties should indicate exact equality
//
//                    val fullySortedOrder = CCsSorted.flatten()
//                    if( fullySortedOrder != node.inputs ) { // we changed the order of inputs
//                        inputAttributePositions = fullySortedOrder.map { createAttributePositionList(it, attrPosMemo) }
//                        node.inputs.clear()
//                        node.inputs += fullySortedOrder
//                    }
//                } else {
//                    // not commutative; fixed order of inputs
//                }
//                val joinHashString = joinConditionsToSortedString(getJoinConditions(node.inputs, inputAttributePositions), inputHashMap)
//                node.inputs.joinToString(prefix = "${node.op} (", postfix = ")", separator = "_") { inputHashMap[it]!!.toString() }
//                        .plus("~~")
//                        .plus(joinHashString)
////                        .also { println(it) }
//                        .hashCode()
//            }
//            is ENode -> throw IllegalStateException("There should not be an ENode present during hash")
//            else -> throw IllegalStateException("Unrecognized: $node")
//        }
////        println("(${node.id}) $node ==> $h")
//        memo[node.id] = h
//        return h */
    }

    fun copyToNormalFormAndHash(node: SNode, memo: MutableMap<Id, String>, attrPosMemo: MutableMap<Id, List<AB>>): Rep {
        if (isNormalForm(node))
            return hash(node, memo, attrPosMemo)
        // copy all nodes down to the base nodes (non-*/Σ/+).
        val newCopy = node.deepCopyToBase()
        assert(newCopy !== node)
        val h = hash(newCopy, memo, attrPosMemo)
        stripDead(newCopy)
        return h
    }

    fun isNormalForm(node: SNode): Boolean {
        return checkPlus(node)
    }

    private fun checkPlus(node: SNode): Boolean {
        return if (node is SNodeNary && node.op == SNodeNary.NaryOp.PLUS) {
            node.inputs.all { checkAgg(it) }
        } else checkAgg(node)
    }

    private fun checkAgg(node: SNode): Boolean {
        return if (node is SNodeAggregate && node.op == Hop.AggOp.SUM) {
            checkMult(node.input)
        } else checkMult(node)
    }

    private fun checkMult(node: SNode): Boolean {
        return if (node is SNodeNary && node.op == SNodeNary.NaryOp.MULT) {
            node.inputs.all { checkBase(it) }
        } else checkBase(node)
    }

    private fun checkBase(node: SNode): Boolean {
        val okNode = !(node is SNodeNary && node.op == SNodeNary.NaryOp.PLUS ||
                node is SNodeAggregate && node.op == Hop.AggOp.SUM ||
                node is SNodeNary && node.op == SNodeNary.NaryOp.MULT)
        return okNode && node.inputs.all { checkPlus(it) }
    }

    fun hashNormalFormKeepAttrPosTop(node: SNode): Pair<Rep, List<AB>> {
        val attrPosMemo = mutableMapOf<Id, List<AB>>()
        val hash = hash(node, mutableMapOf(), attrPosMemo)
        return hash to createAttributePositionList(node, attrPosMemo)
    }

    private fun <A : Comparable<A>, B : Comparable<B>> pairComparator(): Comparator<Pair<A,B>> {
        return Comparator.comparing<Pair<A,B>,A> { it.first }.thenComparing<B> { it.second }
    }
    private fun <T, A : Comparable<A>, B : Comparable<B>> secondPairComparator(): Comparator<Pair<T,Pair<A,B>>> {
        return Comparator.comparing<Pair<T,Pair<A,B>>,A> { it.second.first }.thenComparing<B> { it.second.second }
    }

    /**
     * <pre> <index of input in nodeList>:<position of join condition in input> </pre>
     * sorted by appearance in nodeList and by position of appearance
     * `0:0=2:1,0:1=1:0=2:0,1:1=3:0`
     */
    private fun joinConditionsToSortedString(inputIdxs: List<InputIdx>, nodeList: List<SNode>, _jcs: List<JoinCondition>): String {
        return inputIdxs.fold(_jcs to "") { (jcs, str), iidx ->
            val (overlap, noOverlap) = jcs.partition { iidx in it.inputIdxPresent }
            val overlapSorted = overlap.sortedBy { nodeList[iidx].schema.names.indexOf(it.attribute) }
            val newStr = (if (str.isEmpty()) "" else ",") + overlapSorted.map { jc ->
                jc.inputsWithPosition.map { (jcn, pos) -> "$jcn:$pos" }
                        .sorted()
                        .reduce(String::plus)
            }
            noOverlap to newStr
        }.second
    }

    private data class JoinCondition(
            val attribute: AB,
            val inputsWithPosition: List<Pair<InputIdx, AttrPosition>>
    ) {
        val inputIdxPresent: Set<InputIdx> = inputsWithPosition.map { (idx, _) -> idx }.toSet()
        fun toStringReferenceIndex(): String {
            return inputsWithPosition.sortedWith(CompareConditionPart)
                    .map { (iidx, pos) -> "$iidx.$pos" }
                    .joinToString("=")
        }
        fun toStringReferenceName(names: List<String>, without: InputIdx? = null): String {
            return (if(without != null) inputsWithPosition
                    else inputsWithPosition.filter { (iidx, _) -> iidx != without })
                    .map { (iidx, pos) -> "${names[iidx]}.$pos" }
                    .joinToString("=")
        }
        companion object {
            private val CompareConditionPart: Comparator<Pair<InputIdx, AttrPosition>> =
                    Comparator.comparing<Pair<InputIdx, AttrPosition>, InputIdx>{ it.first }
                            .thenComparing<AttrPosition>{it.second}

//            fun listToStringReferenceIndex(jcs: List<JoinCondition>): String {
//                return jcs.joinToString(",", "[", "]") { it.toStringReferenceIndex() }
//            }
//            fun listToStringReferenceName(jcs: List<JoinCondition>, names: List<String>): String {
//                return jcs.joinToString(",", "[", "]") { it.toStringReferenceName(names) }
//            }
        }
    }

    private fun getJoinConditions(inputs: List<SNode>, inputAttributePositions: List<List<AB>>): List<JoinCondition> {
        val nameToInput = inputs.indices
                .zip(inputAttributePositions)
                .flatMap { (inIdx, positions) -> inputs[inIdx].schema.names.map { it as AB to (inIdx as InputIdx to positions) } }
                .groupBy { it.first }
                .filterValues { it.size > 1 }
                .mapValues { it.value.map { it.second } }
        return nameToInput.map { (n,incidentNodesAndPositions) ->
            val nodesWithJoinPosition = incidentNodesAndPositions.map { (incidentNode, positions) ->
                incidentNode to positions.indexOf(n) as AttrPosition
            }
            JoinCondition(n, nodesWithJoinPosition)
        }
    }

    /**
     * Partition the inputs of an SNodeNary into connected components,
     * wherein two inputs are in the same component if they overlap in at least one name.
     */
    private fun partitionInputIndicesByJoinConditions(inputs: List<SNode>): List<List<InputIdx>> {
        val components: MutableList<List<InputIdx>> = mutableListOf()
        val remaining: MutableList<InputIdx> = inputs.indices.toMutableList()
        while (remaining.isNotEmpty()) {
            components += extractOneComponentByJoinConditions(inputs, remaining)
        }
        return components
    }

    /**
     * Extracts one connected component from [remaining] (modifying it in place) and returns the component.
     * Assumes that [remaining] is not empty.
     */
    @Suppress("UNCHECKED_CAST")
    private fun extractOneComponentByJoinConditions(inputs: List<SNode>, remaining: MutableList<InputIdx>): List<InputIdx> {
        val component = mutableListOf<InputIdx>()
        component.add(remaining.removeAt(0))
        val componentAttributes = mutableSetOf<AB>()
        componentAttributes += inputs[component[0]].schema.names as Set<AB>
        do {
            val modify = remaining.filterInPlace { idx ->
                val idxNode = inputs[idx]
                if( !idxNode.schema.names.disjoint(componentAttributes) ) {
                    component += idx
                    componentAttributes += idxNode.schema.names as Set<AB>
                    false
                } else true
            }
        } while (modify)
        return component
    }



}
package org.apache.sysml.hops.spoof2.enu

import com.google.common.collect.HashMultimap
import com.google.common.collect.Multimap
import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.Schema
import org.apache.sysml.hops.spoof2.plan.mapInPlace

class ENode(schema: Schema) : SNode() {
    init {
        this.schema.setTo(schema)
        this.schema.names.mapInPlace { it.substring(0,1) } // force all unbound
    }

    /** These correspond to the SNodes in [inputs]. */
    val ePaths: ArrayList<EPath> = arrayListOf()

    override fun refreshSchema() {}
    override fun toString() = "ENode"
    override fun checkArity() {}
    override fun shallowCopyNoParentsYesInputs(): SNode {
        TODO("not implemented")
    }
    override fun compare(o: SNode): Boolean {
        return false
    }

    fun addNewEPath(newTopInput: SNode) {
        val ePath = EPath(this, newTopInput)
        inputs += newTopInput
        newTopInput.parents += this
        ePaths += ePath
    }

    fun getContingentENodes(): Set<ENode> {
        return ePaths.flatMap { ePath ->
            ePath.contingencyCostMod.keySet().map { it.eNode }
        }.toSet()
    }

//    private var pathsWithContingencies: List<EPath>? = null
//    fun cachePathsWithContingencies(): List<EPath> {
//        if( pathsWithContingencies == null) {
//            pathsWithContingencies = ePaths.filter { !it.contingencyCostMod.isEmpty }
//        }
//        return pathsWithContingencies!!
//    }

//    fun costLowerBound(): SPCost {
//        // least cost is if the cheapest ePath is selected with maximum overlap with other ePaths
//        return this.ePaths.minBy { it.leastPossibleCost() }?.leastPossibleCost() ?: SPCost.ZERO_COST
//    }
//    fun costUpperBound(): SPCost {
//        // greatest cost is if the most expensive ePath is selected out of all the ones that could reduce others' costs
//        // (or the cheapest path if there are no paths that could reduce others' costs)
//        return costLowerBound().max(
//                this.ePaths.filter { it.canReduceOthersCost() }
//                .maxBy { it.greatestPossibleCost() }?.greatestPossibleCost() ?: SPCost.ZERO_COST
//        )
//    }
}

//sealed class ParentPath {
//    abstract val pathParent: SNode
//}

class EPath(
        val eNode: ENode,
        val input: SNode,
        var costNoContingent: SPCost = SPCost.ZERO_COST,
        val contingencyCostMod: Multimap<EPath, Pair<SNode, SPCost>> = HashMultimap.create()
) { //: ParentPath()

//    fun leastPossibleCost(): SPCost {
//        return costNoContingent - ( contingencyCostReduceThis
//                .maxBy { (_, n) -> n.cachedCost }?.value?.cachedCost ?: SPCost.ZERO_COST)
//    }
//    fun greatestPossibleCost(): SPCost {
//        return costNoContingent
//    }
//    val contingencyCostReduceThis = Multimaps.filterKeys(contingencyCostMod) { otherEPath -> eNode.id > otherEPath!!.eNode.id }
//    fun canHaveCostReducedByOthers() = !contingencyCostReduceThis.isEmpty
//
//    val contingencyCostReduceOther = Multimaps.filterKeys(contingencyCostMod) { otherEPath -> eNode.id < otherEPath!!.eNode.id }
//    fun canReduceOthersCost(): Boolean = !contingencyCostReduceOther.isEmpty

    private fun contingenciesToString(): String {
        if( contingencyCostMod.isEmpty )
            return "{}"
        return contingencyCostMod.asMap().map { (ePath,v) ->
            ePath.shortString() to v.map { (node, cost) -> "${node.id}:$cost" }
        }.toMap().toString()
    }

    override fun toString() =
            "EPath<${eNode.id}>(${input.id}, $costNoContingent, contingent:${contingenciesToString()})"
    fun shortString(): String {
        return "EPath<${eNode.id}>(${input.id})"
    }

    private var _contingentPathToSavings_groupByENode: List<Pair<ENode, List<Pair<EPath, SPCost>>>>? = null
    internal fun contingentPathToSavings_groupByENode(): List<Pair<ENode, List<Pair<EPath, SPCost>>>> {
        if( _contingentPathToSavings_groupByENode == null) {
            _contingentPathToSavings_groupByENode = contingencyCostMod.asMap().map { (ePath, list) ->
                (ePath to list.fold(SPCost.ZERO_COST) { acc, (_, cost) -> acc + cost })
            }.groupBy { it.first.eNode }.toList()
        }
        return _contingentPathToSavings_groupByENode!!
    }


}
//data class RootPath(
//        override val pathParent: SNode
//) : ParentPath()


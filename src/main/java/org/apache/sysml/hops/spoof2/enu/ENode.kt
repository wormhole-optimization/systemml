package org.apache.sysml.hops.spoof2.enu

import com.google.common.collect.HashMultimap
import com.google.common.collect.Multimap
import org.apache.sysml.hops.spoof2.plan.*
import java.util.*
//
//class ENode private constructor() : SNode() {
//
//    override fun _shallowCopy(newInputs: List<SNode>) = ENode().also { en ->
//        en.schema.setTo(this.schema)
//        en.inputs += newInputs
//        newInputs.forEach { it.parents += en }
//    }
//
//    constructor(schema: Map<Attribute.Unbound, Pair<AB, Shape>>) : this() {
//        schema.forEach { au, e ->
//            this.schema.put(au, e.second)
//        }
//    }
//
//    /** These correspond to the SNodes in [inputs]. */
//    val ePaths: ArrayList<EPath> = arrayListOf()
//
//    override fun refreshSchema() {}
//    override fun toString() = "ENode"
//    override fun checkArity() {}
//    override fun compare(o: SNode): Boolean {
//        return false
//    }
//
//    fun addNewEPath(newTopInput: SNode) {
//        val ePath = EPath(this, newTopInput)
//        inputs += newTopInput
//        newTopInput.parents += this
//        ePaths += ePath
//    }
//
//    fun getContingentENodes(): Set<ENode> {
//        return ePaths.flatMap { ePath ->
//            ePath.contingencyCostMod.keySet().map { it.eNode }
//        }.toSet()
//    }
//
////    private var pathsWithContingencies: List<EPath>? = null
////    fun cachePathsWithContingencies(): List<EPath> {
////        if( pathsWithContingencies == null) {
////            pathsWithContingencies = ePaths.filter { !it.contingencyCostMod.isEmpty }
////        }
////        return pathsWithContingencies!!
////    }
//
////    fun costLowerBound(): SPCost {
////        // least cost is if the cheapest ePath is selected with maximum overlap with other ePaths
////        return this.ePaths.minBy { it.leastPossibleCost() }?.leastPossibleCost() ?: SPCost.ZERO_COST
////    }
////    fun costUpperBound(): SPCost {
////        // greatest cost is if the most expensive ePath is selected out of all the ones that could reduce others' costs
////        // (or the cheapest path if there are no paths that could reduce others' costs)
////        return costLowerBound().max(
////                this.ePaths.filter { it.canReduceOthersCost() }
////                .maxBy { it.greatestPossibleCost() }?.greatestPossibleCost() ?: SPCost.ZERO_COST
////        )
////    }
//}
//
////sealed class ParentPath {
////    abstract val pathParent: SNode
////}
//
//class EPath(
//        val eNode: ENode,
//        var input: SNode,
//        var costNoContingent: SPCost = SPCost.ZERO_COST,
//        val contingencyCostMod: Multimap<EPath, EPathShare> = HashMultimap.create()
//) { //: ParentPath()
//
////    fun leastPossibleCost(): SPCost {
////        return costNoContingent - ( contingencyCostReduceThis
////                .maxBy { (_, n) -> n.cachedCost }?.value?.cachedCost ?: SPCost.ZERO_COST)
////    }
////    fun greatestPossibleCost(): SPCost {
////        return costNoContingent
////    }
////    val contingencyCostReduceThis = Multimaps.filterKeys(contingencyCostMod) { otherEPath -> eNode.id > otherEPath!!.eNode.id }
////    fun canHaveCostReducedByOthers() = !contingencyCostReduceThis.isEmpty
////
////    val contingencyCostReduceOther = Multimaps.filterKeys(contingencyCostMod) { otherEPath -> eNode.id < otherEPath!!.eNode.id }
////    fun canReduceOthersCost(): Boolean = !contingencyCostReduceOther.isEmpty
//
//    private fun contingenciesToString(): String {
//        if( contingencyCostMod.isEmpty )
//            return "{}"
//        return contingencyCostMod.asMap().map { (ePath,v) ->
//            ePath.shortString() to v.map { share ->
//                "${share.shareNode.id}:${share.cost}${if(share.shadowedBy.isNotEmpty()) "^${share.shadowedBy.map { it.shortString() }}^" else ""}"
//            }
//        }.toMap().toString()
//    }
//
//    override fun toString() =
//            "EPath<${eNode.id}>(${input.id}, $costNoContingent, contingent:${contingenciesToString()})"
//    fun shortString(): String {
//        return "EPath<${eNode.id}>(${input.id})"
//    }
//
//    class EPathShare(
//            val ePath: EPath,
//            val cost: SPCost,
//            val shareNode: SNode,
//            val shadowedBy: Set<EPath>
//    ) {
//        override fun toString() =
//                "EPathShare(${ePath.shortString()}, $cost, shareNode=${shareNode.id}$shareNode)"
//    }
//
//    // sorted by eNode, then by ePath
//    private var _pathShares_groupByENode: List<GroupENode>? = null
//    internal fun pathShares_groupByENode(): List<GroupENode> {
//        if( _pathShares_groupByENode == null) {
//            _pathShares_groupByENode = contingencyCostMod.asMap().entries.groupBy { it.key.eNode }
//                    .mapValues { (_, list) ->
//                        list.flatMap { it.value }.groupBy { it.ePath }.toList().sortedBy { it.first.input.id } //.map { it.second }
//                        //list.fold(SPCost.ZERO_COST) { acc, (_, cost) -> acc + cost }
//                    }.toList().sortedBy { it.first.id } //.map { it.second }
//        }
//        return _pathShares_groupByENode!!
//    }
//
//    companion object {
//        private fun rFindParentIn(curPath: EPath, eligibleShareNodes: Set<SNode>, node: SNode): Boolean {
//            if( node in eligibleShareNodes )
//                return true
//            return node.parents.filter { it.ePathLabels.size > 1 && curPath in it.ePathLabels }
//                    .any { rFindParentIn(curPath, eligibleShareNodes, it) }
//        }
//
//        fun filterNotOverlapping(curPath: EPath, x: Collection<EPathShare>): List<EPathShare> {
//            val pathsPresent = x.map { it.ePath }.toSet()
//            val pathShares = ArrayList(x)
//            // remove those pathShares that overlap with a lesser one
//            x.forEach { pathShare ->
//                val otherLabels = pathShare.shareNode.ePathLabels.filter { pathLabel ->
//                    pathLabel != pathShare.ePath
//                            && pathLabel != curPath
//                            && pathLabel in pathsPresent // I think this includes the pathLabel != curPath case
//                }
//                if( otherLabels.isNotEmpty() ) {
//                    // bad case - try to find a different pathShare in the parents of this shareNode
//                    // if we find one, then discount this. Otherwise keep it.
//                    val otherShareNodes = pathShares.filter { it != pathShare && it.ePath in otherLabels }
//                            .map { it.shareNode }.toSet()
//                    if( rFindParentIn(curPath, otherShareNodes, pathShare.shareNode) )
//                        pathShares -= pathShare
//                }
//            }
//            return pathShares
//        }
//    }
//
//}
//
//
//typealias GroupEPath = Pair<EPath, List<EPath.EPathShare>>
//typealias GroupENode = Pair<ENode, List<GroupEPath>>
//
//fun GroupEPath.sumShares(): SPCost = this.second.fold(SPCost.ZERO_COST) { acc, share -> acc + share.cost}
//fun GroupEPath.shares(): List<EPath.EPathShare> = this.second
//fun GroupENode.flatShares(): List<EPath.EPathShare> = this.second.flatMap { it.shares() }
//

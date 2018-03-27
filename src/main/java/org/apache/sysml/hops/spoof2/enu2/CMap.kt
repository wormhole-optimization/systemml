package org.apache.sysml.hops.spoof2.enu2

import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.makeRenameAbove
import org.apache.sysml.hops.spoof2.plan.toDenseString
import java.util.*

class CMap(
        val construct: Construct,
//        val children: List<CMap>,
        val tgtGraph: Int,
        val vertMap: List<ABS>,
        val coveredEdges: BooleanArray // size tgtEdgeListNoScalars
) {
    val complete: Boolean = coveredEdges.all { it } && vertMap.size == BottomUpOptimize.buo.tgs.tgts[tgtGraph].outs.size

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as CMap

        if (tgtGraph != other.tgtGraph) return false
        if (vertMap != other.vertMap) return false
        if (construct != other.construct) return false
//        if (children != other.children) return false
        if (!Arrays.equals(coveredEdges, other.coveredEdges)) return false

        return true
    }
    override fun hashCode(): Int {
        var result = construct.hashCode()
        result = 31 * result + tgtGraph
//        result = 31 * result + children.hashCode()
        result = 31 * result + vertMap.hashCode()
        result = 31 * result + Arrays.hashCode(coveredEdges)
        return result
    }

    override fun toString(): String {
        return "CMap<$tgtGraph>[${coveredEdges.toDenseString()}]"
    }

//    // the ABList of the returned SNode is exactly the vertMap
//    fun convertToSNode(): SNode {
//        children.map { child ->
//            val cn = child.convertToSNode()
//            // cn's ordered schema is exactly its vertMap
//            cn
//        }
//        cons
//    }
}


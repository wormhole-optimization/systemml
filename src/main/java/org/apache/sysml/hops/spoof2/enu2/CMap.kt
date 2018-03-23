package org.apache.sysml.hops.spoof2.enu2

import java.util.*

class CMap(
        val construct: Construct,
        val tgtGraph: Int,
        val vertMap: List<ABS>,
        val coveredEdges: BooleanArray // size tgtEdgeListNoScalars
) {
    val complete: Boolean = coveredEdges.all { it } && vertMap.size == BottomUpOptimize.buo.tgs.tgts[tgtGraph].outs.size

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as CMap

        if (construct != other.construct) return false
        if (tgtGraph != other.tgtGraph) return false
        if (vertMap != other.vertMap) return false
        if (!Arrays.equals(coveredEdges, other.coveredEdges)) return false

        return true
    }
    override fun hashCode(): Int {
        var result = construct.hashCode()
        result = 31 * result + tgtGraph
        result = 31 * result + vertMap.hashCode()
        result = 31 * result + Arrays.hashCode(coveredEdges)
        return result
    }
}


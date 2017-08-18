package org.apache.sysml.hops.spoof2.enu

import org.apache.sysml.hops.spoof2.plan.SNode

class ENode(initialInput: SNode) : SNode(initialInput) {
    init {
        refreshSchema()
    }
    /** These correspond to the SNodes in [inputs]. */
    val ePaths: ArrayList<EPath> = arrayListOf()

    data class EPath(
            val eNode: ENode,
            val input: SNode,
            val costNoShare: SPCost,
            val contingencyCostMod: MutableMap<EPath, SPCost>
    )

    override fun refreshSchema() {
        schema.setTo(inputs[0].schema)
    }

    override fun toString(): String {
        return "ENode::$ePaths"
    }

    override fun checkArity() {}

    override fun shallowCopyNoParentsYesInputs(): SNode {
        TODO("not implemented")
    }

    override fun compare(o: SNode): Boolean {
        TODO("not implemented")
    }
}
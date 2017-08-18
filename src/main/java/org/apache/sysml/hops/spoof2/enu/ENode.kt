package org.apache.sysml.hops.spoof2.enu

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

    data class EPath(
            val eNode: ENode,
            val input: SNode,
            var costNoShare: SPCost = SPCost.MAX_COST,
            val contingencyCostMod: MutableMap<EPath, SPCost> = mutableMapOf()
    )

    override fun refreshSchema() {}

    override fun toString(): String {
        return "ENode"
    }

    override fun checkArity() {}

    override fun shallowCopyNoParentsYesInputs(): SNode {
        TODO("not implemented")
    }

    override fun compare(o: SNode): Boolean {
        return false
    }

    fun addNewEPath(newTopInput: SNode) {
        val ePath = ENode.EPath(this, newTopInput)
        inputs += newTopInput
        newTopInput.parents += this
        ePaths += ePath
    }
}
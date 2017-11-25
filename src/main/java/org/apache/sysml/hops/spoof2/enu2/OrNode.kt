package org.apache.sysml.hops.spoof2.enu2

import org.apache.sysml.hops.spoof2.plan.SNode

class OrNode(
        inputs: List<SNode>
): SNode(inputs) {

    constructor(vararg inputs: SNode) : this(inputs.asList())

    override fun refreshSchema() {
        this.schema.setTo(inputs[0].schema)
    }

    override fun toString(): String {
        return "OrNode"
    }

    override fun checkArity() {
        this.check(inputs.isNotEmpty()) {"An OrNode should never have no children"}
    }

    override fun _shallowCopy(newInputs: List<SNode>) = OrNode(newInputs)

    override fun compare(o: SNode): Boolean {
        return o is OrNode && inputs == o.inputs
    }

}
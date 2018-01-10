package org.apache.sysml.hops.spoof2.enu2

import org.apache.sysml.hops.spoof2.plan.SNode

// An OrNode's inputs should not have duplicates
class OrNode private constructor(
        inputs: List<SNode>
): SNode(inputs) {
    init {
        refreshSchema()
        if (inputs.map(SNode::schema).toSet().size != 1)
            println("oh")
        check(inputs.map(SNode::schema).toSet().size == 1) {"schema inputs to OrNode disagree: $inputs, ${inputs.map(SNode::schema)}"}
    }

    constructor(vararg inputs: SNode) : this(inputs.toSet().toList())
    constructor(inputs: Set<SNode>) : this(inputs.toList())

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

    fun flatten() {
        do {
            val set = inputs.filterIsInstance(OrNode::class.java).toSet()
            set.forEach { inOr ->
                while (this.inputs.remove(inOr) && inOr.parents.remove(this)) ;
                inOr.parents.forEach { paOr -> paOr.inputs[paOr.inputs.indexOf(inOr)] = this; this.parents += paOr }
                inOr.inputs.forEach { inOrIn -> inOrIn.parents[inOrIn.parents.indexOf(inOr)] = this; this.inputs += inOrIn }
            }
        } while (set.isNotEmpty())
    }

}
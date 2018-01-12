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

    fun flatten(): Boolean {
        var ret = false
        do {
            val set = inputs.filterIsInstance(OrNode::class.java).toSet()
            set.forEach { or ->
                while (this.inputs.remove(or)) or.parents.remove(this)
                or.parents.forEach { pa -> pa.inputs[pa.inputs.indexOf(or)] = this; this.parents += pa }
                or.inputs.forEach { inp ->
                    inp.parents[inp.parents.indexOf(or)] = this
                    if (inp !in this.inputs) // no duplicates
                        this.inputs += inp
                }
            }
            ret = ret || set.isNotEmpty()
        } while (set.isNotEmpty())
        return ret
    }

}
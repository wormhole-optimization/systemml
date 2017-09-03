package org.apache.sysml.hops.spoof2.plan

import org.apache.sysml.hops.Hop.AggOp

/**
 * Aggregate a single input.
 */
class SNodeAggregate private constructor(
        val op: AggOp,
        inputs: List<SNode>,
        aggs0: Collection<Name>
) : SNode(inputs) {
    var input: SNode
        get() = inputs[0]
        set(v) { inputs[0] = v }

    override fun shallowCopyNoParentsYesInputs() = SNodeAggregate(op, inputs, aggs)
    override fun compare(o: SNode) =
            o is SNodeAggregate && o.op == this.op && o.aggs == this.aggs && o.input == this.input

    val aggs: ArrayList<Name> = ArrayList(aggs0)
    init {
        refreshSchema()
    }

    constructor(op: AggOp, input: SNode, names: Collection<Name>) : this(op, listOf(input), names)
    constructor(op: AggOp, input: SNode, vararg names: Name) : this(op, listOf(input), names.asList())

    override fun toString() = "agg(${op.name.toLowerCase()}$aggs)"

    override fun checkArity() {
        this.check( inputs.size == 1 ) {"SNodeAggregate should have 1 input but has ${inputs.size}"}
    }

    override fun refreshSchema() {
        // input names minus aggregated names
        schema.setTo(inputs[0].schema)
        schema.removeBoundAttributes(aggs)
    }
}

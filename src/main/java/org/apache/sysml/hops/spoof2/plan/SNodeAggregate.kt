package org.apache.sysml.hops.spoof2.plan

import org.apache.sysml.hops.Hop.AggOp

/**
 * Aggregate a single input.
 */
class SNodeAggregate(
        val op: AggOp,
        input: SNode,
        aggs: Schema
) : SNode(listOf(input)) {
    var input: SNode
        get() = inputs[0]
        set(v) { inputs[0] = v }

    constructor(op: AggOp, input: SNode, vararg names: AB) :
            this(op, input, input.schema.filterKeys { it in names })
    constructor(op: AggOp, input: SNode, names: Iterable<AB>) :
            this(op, input, input.schema.filterKeys { it in names })

    override fun shallowCopy(newInputs: List<SNode>) = SNodeAggregate(op, newInputs[0], aggs)
    override fun compare(o: SNode) =
            o is SNodeAggregate && o.op == this.op && o.aggs == this.aggs && o.input == this.input

    val aggs: Schema = Schema(aggs)
    init {
        refreshSchema()
    }

    override fun toString() = "agg(${op.name.toLowerCase()}$aggs)"

    override fun checkArity() {
        this.check( inputs.size == 1 ) {"SNodeAggregate should have 1 input but has ${inputs.size}"}
    }

    override fun refreshSchema() {
        // input names minus aggregated names
        schema.setTo(inputs[0].schema)
        schema -= aggs
    }

    fun aggsNotInInputSchema(): Schema {
        return aggs.filterKeys { n -> n !in input.schema }
    }
}

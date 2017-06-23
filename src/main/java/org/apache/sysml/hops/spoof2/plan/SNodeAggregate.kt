package org.apache.sysml.hops.spoof2.plan

import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.Hop.AggOp

class SNodeAggregate(
        val op: AggOp,
        inputs: List<SNode>,
        val labels: HashSet<String>,
        val direction: Hop.Direction = Hop.Direction.RowCol // todo!
) : SNode(inputs) {

    constructor(op: AggOp, input: SNode, labels: HashSet<String>) : this(op, listOf(input), labels)

    override val isSchemaAggregator = false
    override val isSchemaPropagator = true

    override fun toString() = "agg(${op.name.toLowerCase()})"

    override fun checkArity() {
        // can aggregate any number of SNodes
        // todo - what about VAR, MAXINDEX, MININDEX?
    }

    override fun updateSchema() {
        // intersection of input schema labels - this means we may need to add dummy operands to change what we retain in the output schema
        schema.clearLabelsTypes()
        inputs.forEach { schema += it.schema }

        // handle matrix aggregate - transform type based on direction
        val inputType = inputs[0].schema.type
        if (inputType.size <= 1)
        else if (inputType.size > 2)
            throw IllegalStateException("input type has dimension >2 on Schema $this")
        else {
            when (direction) {
                Hop.Direction.Col -> {
                    schema.type += inputType[0]
                    schema.rowVector = true
                }
                Hop.Direction.Row -> {
                    schema.type += inputType[1]
                    schema.rowVector = false
                }
                Hop.Direction.RowCol -> {}
            }
        }
    }
}

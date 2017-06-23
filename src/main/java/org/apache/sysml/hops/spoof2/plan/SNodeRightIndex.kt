package org.apache.sysml.hops.spoof2.plan

/**
 * Begin loop: move the first type dimention to the back of the label dimensions and add a label.
 * todo - should be able to right index a different type dimension than the first (i.e., the rows of a matrix)
 */
class SNodeRightIndex(
        input: SNode
) : SNode(input) {

    var label: String = Schema.nextLabel()

    override val isSchemaAggregator = false
    override val isSchemaPropagator = false

    override fun toString() = "ri($label)"

    override fun checkArity() {
        this.check( inputs.size == 1 ) {"must have one input but has $inputs"}
    }

    override fun updateSchema() {
        val si = inputs[0].schema
        this.check( si.type.isNotEmpty() ) {"attempt to right index an SNode with scalar type dimension: $si"}
        val td = si.type.first()
        val ts = si.type.size
        schema.clearLabelsTypes()

        schema.labels.addAll(si.labels)
        schema.labels += label
        schema.dims.addAll(si.dims)
        schema.dims += td
        schema.setType(si.type.subList(1, ts), si.rowVector)
    }
}

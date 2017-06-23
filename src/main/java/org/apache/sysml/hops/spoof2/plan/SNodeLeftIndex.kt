package org.apache.sysml.hops.spoof2.plan

/**
 * End loop: move the last label to the front of the type dimensions.
 */
class SNodeLeftIndex(
        input: SNode
) : SNode(input) {

    override val isSchemaAggregator = true
    override val isSchemaPropagator = false

    override fun toString() = "li()"

    override fun checkArity() {
        this.check( inputs.size == 1 ) {"must have one input but has $inputs"}
    }

    override fun updateSchema() {
        val si = inputs[0].schema
        this.check( si.labels.isNotEmpty() ) {"attempt to left index an SNode with no labels: $si"}
        val ld = si.dims.last()
        val ls = si.dims.size
        schema.clearLabelsTypes()

        schema.labels.addAll(si.labels.subList(0, ls-1))
        schema.dims.addAll(si.dims.subList(0, ls-1))
        schema.type += ld
        schema.setType(si.type, si.rowVector)
    }
}

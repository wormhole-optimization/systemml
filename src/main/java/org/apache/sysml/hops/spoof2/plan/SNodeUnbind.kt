package org.apache.sysml.hops.spoof2.plan

/**
 * Unbind attributes.
 */
class SNodeUnbind(
        input: SNode,
        names: Collection<Name>
) : SNode(input) {
    val unbinding = ArrayList(names)
    init {
        refreshSchema()
    }

    override fun toString() = "ub$unbinding"

    override fun checkArity() {
        this.check( inputs.size == 1 ) {"must have one input but has $inputs"}
    }

    override fun refreshSchema() {
        val si = inputs[0].schema
        this.check( unbinding.all(si::contains) ) {"attempt to unbind $unbinding on input schema $si"}
        schema.setTo(si)
        unbinding.forEach(schema::unbindName)
    }
}

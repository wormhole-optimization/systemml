package org.apache.sysml.hops.spoof2.plan

/**
 * Unbind attributes.
 */
class SNodeUnbind(
        input: SNode,
        names: Map<Int,Name>
) : SNode(input) {
    val unbinding: MutableMap<Int,Name> = HashMap(names) // defensive copy
    init {
        refreshSchema()
    }

    override fun toString() = "ub$unbinding"

    override fun checkArity() {
        this.check( inputs.size == 1 ) {"must have one input but has $inputs"}
    }

    override fun refreshSchema() {
        val si = inputs[0].schema
        this.check( unbinding.values.all(si::contains) ) {"attempt to unbind $unbinding on input schema $si"}
        schema.setTo(si)
        val pmap = unbinding.mapValues { (_,v) -> schema.names.indexOf(v) }
        schema.permutePositions(pmap)
        unbinding.values.forEach(schema::unbindName)
    }
}

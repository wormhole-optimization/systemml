package org.apache.sysml.hops.spoof2.plan

/**
 * Unbind attributes.
 */
class SNodeUnbind(
        input: SNode,
        names: Map<Int,Name>
) : SNode(input) {
    val unbindings: HashMap<Int,Name> = HashMap(names) // defensive copy
    init {
        refreshSchema()
    }

    override fun toString() = "ub$unbindings"

    override fun checkArity() {
        this.check( inputs.size == 1 ) {"must have one input but has $inputs"}
    }

    override fun refreshSchema() {
        val si = inputs[0].schema
        this.check( unbindings.values.all(si::contains) ) {"attempt to unbind $unbindings on input schema $si"}
        schema.setTo(si)
        val pmap = unbindings.mapValues { (_,v) -> schema.names.indexOf(v) }
        schema.permutePositions(pmap)
        unbindings.values.forEach(schema::unbindName)
    }
}
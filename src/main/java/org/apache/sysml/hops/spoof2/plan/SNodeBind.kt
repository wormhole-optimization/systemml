package org.apache.sysml.hops.spoof2.plan

/**
 * Bind attributes.
 */
class SNodeBind(
        input: SNode,
        bindings: Map<Int, Name>
) : SNode(input) {
    val bindings: MutableMap<Int, Name> = HashMap(bindings)
    init {
        refreshSchema()
    }

    override fun toString() = "bi$bindings"

    override fun checkArity() {
        this.check( inputs.size == 1 ) {"must have one input but has $inputs"}
    }

    override fun refreshSchema() {
        val si = inputs[0].schema
        this.check(bindings.keys.none(si::isBound)) { "attempt to bind by $bindings on input schema $si" }
        schema.setTo(si)
        bindings.forEach(schema::bindName)
    }
}

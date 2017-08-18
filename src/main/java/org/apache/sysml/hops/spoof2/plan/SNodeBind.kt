package org.apache.sysml.hops.spoof2.plan

/**
 * Bind attributes.
 */
class SNodeBind(
        input: SNode,
        bindings: Map<Int, Name>
) : SNode(input) {
    var input: SNode
        get() = inputs[0]
        set(v) { inputs[0] = v }

    /** Bind all unbound attributes in the input's schema. */
    constructor(input: SNode)
            : this(input, input.schema)
    constructor(input: SNode, schema: Schema)
            : this(input, schema.names.mapIndexed { i, n -> i to n }.filter { (_, n) -> !n.isBound() }.toMap())

    override fun compare(o: SNode) =
            o is SNodeBind && o.bindings == this.bindings && o.input == this.input

    override fun shallowCopyNoParentsYesInputs() = SNodeBind(input, bindings)
    val bindings: MutableMap<Int, Name> = HashMap(bindings) // defensive copy

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

package org.apache.sysml.hops.spoof2.plan

/**
 * Unbind attributes.
 */
class SNodeUnbind(
        input: SNode,
        names: Map<Int,Name>
) : SNode(input) {
    var input: SNode
        get() = inputs[0]
        set(v) { inputs[0] = v }

    /** Unbind all bound attributes in the input's schema. */
    constructor(input: SNode)
            : this(input, input.schema.names.mapIndexed { i, n -> i to n }.filter { (_, n) -> n.isBound() }.toMap())

    override fun compare(o: SNode) =
            o is SNodeUnbind && this.unbindings == o.unbindings && this.input == o.input

    override fun shallowCopyNoParentsYesInputs() = SNodeUnbind(input, unbindings)

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

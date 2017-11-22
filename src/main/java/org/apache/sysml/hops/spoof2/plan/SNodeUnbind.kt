package org.apache.sysml.hops.spoof2.plan

import com.google.common.collect.BiMap
import com.google.common.collect.HashBiMap

/**
 * Unbind attributes.
 */
class SNodeUnbind(
        input: SNode,
        names: Map<AU, AB>
) : SNode(input) {
    var input: SNode
        get() = inputs[0]
        set(v) { inputs[0] = v }

    val unbindings: BiMap<AU, AB> = HashBiMap.create(names) // defensive copy

    override fun compare(o: SNode) =
            o is SNodeUnbind && this.unbindings == o.unbindings && this.input == o.input
    override fun _shallowCopy(newInputs: List<SNode>) = SNodeUnbind(newInputs[0], unbindings)
    init {
        refreshSchema()
    }

    override fun toString() = "ub${unbindings.toSortedMap()}"

    override fun checkArity() {
        this.check( inputs.size == 1 ) {"must have one input but has $inputs"}
    }

    override fun refreshSchema() {
        val si = inputs[0].schema
        this.check( unbindings.values.all { it in si } ) {"attempt to unbind $unbindings on input schema $si"}
        schema.setTo(si)
        unbindings.forEach { d, b -> schema.replaceKey(b, d) }
    }
}

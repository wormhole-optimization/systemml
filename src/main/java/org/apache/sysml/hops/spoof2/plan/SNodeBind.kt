package org.apache.sysml.hops.spoof2.plan

import com.google.common.collect.BiMap
import com.google.common.collect.HashBiMap

/**
 * Bind attributes.
 */
class SNodeBind(
        input: SNode,
        bindings: Map<AU, AB>
) : SNode(input) {
    var input: SNode
        get() = inputs[0]
        set(v) { inputs[0] = v }

    val bindings: BiMap<AU, AB> = HashBiMap.create(bindings) // defensive copy

    override fun compare(o: SNode) =
            o is SNodeBind && o.bindings == this.bindings && o.input == this.input
    override fun _shallowCopy(newInputs: List<SNode>) = SNodeBind(newInputs[0], bindings)

    init {
        refreshSchema()
    }

    override fun toString() = "bi${bindings.toSortedMap()}"

    override fun checkArity() {
        this.check( inputs.size == 1 ) {"must have one input but has $inputs"}
    }

    override fun refreshSchema() {
        val si = inputs[0].schema
        schema.setTo(si)
        bindings.forEach { d, b -> schema.replaceKey(d, b) }
    }
}

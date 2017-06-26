package org.apache.sysml.hops.spoof2.plan

import com.google.common.collect.HashMultiset
import com.google.common.collect.Multiset
import org.apache.sysml.hops.spoof2.plan.SNodeNary.NaryOp.*

class SNodePermute(
        input: SNode,
        permutation: Map<Name, Name>
) : SNode(listOf(input)) {
    val permutation: MutableMap<Name, Name> = HashMap(permutation)
    init {
        refreshSchema()
    }

    override fun toString() = "tr$permutation"

    override fun checkArity() {
        this.check(1 == inputs.size) {"permute should have arity 1 but has arity ${inputs.size}"}
    }

    override fun refreshSchema() {
        schema.setTo(inputs[0].schema)
        schema.permute(permutation)
    }

    /**
     * Get the attributes that are changed in this permutation.
     */
    fun getSwitchedAttributes(): List<Name> {
        return permutation.map { (k,v) -> if( k != v ) k else null }.filterNotNull()
    }
}

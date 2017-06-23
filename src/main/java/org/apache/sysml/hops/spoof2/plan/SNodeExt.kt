package org.apache.sysml.hops.spoof2.plan

import org.apache.sysml.hops.Hop

class SNodeExt(
        val hop: Hop,
        inputs: List<SNode>
) : SNode(inputs) {

    constructor(hop: Hop, vararg inputs: SNode) : this(hop, inputs.asList())

    override val isSchemaAggregator = false
    override val isSchemaPropagator = false

    override fun toString() = "ext(${hop.hopID} ${hop.opString})"

    override fun checkArity() {
        // no check
    }

    override fun updateSchema() {
        // treat like Nary to put something here
        schema.clearLabelsTypes()
        inputs.forEach { schema += it.schema }
        // operator dg(rand) is classified as an ext
//        if( inputs.isNotEmpty() ) {
//            // suppose the input type is the same...
//            schema.setType(inputs[0].schema.type, inputs[0].schema.rowVector)
//        } else {
            // dg(rand)
            if (hop.dim1 == 1L) {
                if (hop.dim2 != 1L)
                    schema.setType(hop.dim2, rowVector = true)
            } else {
                if (hop.dim2 == 1L)
                    schema.setType(hop.dim1, rowVector = false)
                else
                    schema.setType(hop.dim1, hop.dim2)
            }
//        }
    }
}

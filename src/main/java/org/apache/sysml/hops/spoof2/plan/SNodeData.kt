package org.apache.sysml.hops.spoof2.plan

import org.apache.sysml.hops.DataOp
import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.LiteralOp
import org.apache.sysml.parser.Expression

// DataOp or LiteralOp
class SNodeData(
        val hop: Hop,
        vararg inputs: SNode
) : SNode(*inputs) {
    val isLiteral = hop is LiteralOp

    constructor(input: SNode, hop: Hop) : this(hop, input)

    override val isSchemaAggregator = false

    override val isSchemaPropagator = false

    override fun toString(): String {
        return "data(${hop.hopID} ${hop.opString})"
    }

    override fun checkArity() {
        if( hop is LiteralOp || hop is DataOp && hop.isRead )
            this.check( inputs.isEmpty() ) {"SNodeData read should have no inputs but has $inputs"}
        else if( hop is DataOp && hop.isWrite )
            this.check( inputs.size == 1 ) {"SNodeData write should have 1 input but has $inputs"}
        else TODO("unknown hop origin")
    }

    override fun updateSchema() {
        assert(hop.dimsKnown()) {"dims not known for hop ${hop.hopID} ${hop.opString}"}
        schema.clearLabelsTypes()

        if( hop.dataType == Expression.DataType.SCALAR )
        else if( hop.dim1 == 1L ) {
            schema.type += hop.dim2
            schema.rowVector = true
        }
        else if( hop.dim2 == 1L ) {
            schema.type += hop.dim2
            schema.rowVector = false
        }
        else {
            schema.type += hop.dim1
            schema.type += hop.dim2
        }
    }
}

package org.apache.sysml.hops.spoof2.plan

import org.apache.sysml.hops.DataOp
import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.LiteralOp
import org.apache.sysml.parser.Expression

/**
 * DataOp (read or write) or LiteralOp.
 */
class SNodeData private constructor(
        val hop: Hop,
        input: List<SNode>
) : SNode(input) {
    override fun shallowCopyNoParentsYesInputs() = SNodeData(hop, inputs)

    constructor(hop: Hop): this(hop, listOf())

    override fun compare(o: SNode) =
            o is SNodeData && o.hop == this.hop && o.inputs == this.inputs

    constructor(hop: Hop, input: SNode): this(hop, listOf(input))

    val isLiteral = hop is LiteralOp
    val isWrite = hop is DataOp && hop.isWrite

    val literalLong: Long
        get() {
            check(hop is LiteralOp) {"tried to get literal value of non-literal $this id=$id"}
            return (hop as LiteralOp).longValue
        }
    val literalDouble: Double
        get() {
            check(hop is LiteralOp) {"tried to get literal value of non-literal $this id=$id"}
            return (hop as LiteralOp).doubleValue
        }

//    val inputHopClasses = hop.input.map(Hop::classify)

    override fun toString() = "data(${hop.hopID} ${hop.opString})"

    override fun checkArity() {
        if( isWrite )
            this.check( inputs.size == 1 ) {"SNodeData write should have 1 input but has $inputs"}
        else
            this.check( inputs.isEmpty() ) {"SNodeData read should have no inputs but has $inputs"}
    }
    
    // constant schema
    init {
        assert(hop.dimsKnown()) {"dims not known for hop ${hop.hopID} ${hop.opString}"}

        if( hop.dataType == Expression.DataType.SCALAR || hop.dim1 == 1L && hop.dim2 == 1L )
        else if( hop.dim1 == 1L )
            schema.addUnboundAttribute(hop.dim2, Schema.NamePrefix.ROW)
        else if( hop.dim2 == 1L )
            schema.addUnboundAttribute(hop.dim1, Schema.NamePrefix.COL)
        else {
            schema.addUnboundAttribute(hop.dim1, Schema.NamePrefix.ROW)
            schema.addUnboundAttribute(hop.dim2, Schema.NamePrefix.COL)
        }
    }

    override fun refreshSchema() {
        // schema never changes
    }
}

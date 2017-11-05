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
    override fun shallowCopy(newInputs: List<SNode>) = SNodeData(hop, newInputs)

    constructor(hop: Hop): this(hop, listOf())

    override fun compare(o: SNode) =
            o is SNodeData && o.hop == this.hop && o.inputs == this.inputs

    constructor(hop: Hop, input: SNode): this(hop, listOf(input))

    val isLiteral = hop is LiteralOp
    val isLiteralNumeric = hop is LiteralOp && when( hop.valueType!! ) {
        Expression.ValueType.STRING, Expression.ValueType.OBJECT, Expression.ValueType.UNKNOWN -> false
        Expression.ValueType.BOOLEAN, Expression.ValueType.INT, Expression.ValueType.DOUBLE -> true
    }
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
            schema.put(AU.U0, hop.dim2)
        else if( hop.dim2 == 1L )
            schema.put(AU.U0, hop.dim1)
        else {
            schema.put(AU.U0, hop.dim1)
            schema.put(AU.U1, hop.dim2)
        }
    }

    override fun refreshSchema() {
        // schema never changes
    }
}

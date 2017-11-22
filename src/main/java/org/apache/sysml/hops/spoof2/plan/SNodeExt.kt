package org.apache.sysml.hops.spoof2.plan

import org.apache.sysml.hops.Hop
import org.apache.sysml.parser.Expression

class SNodeExt(
        val hop: Hop,
        inputs: List<SNode>
) : SNode(inputs) {
    override fun _shallowCopy(newInputs: List<SNode>) = SNodeExt(hop, newInputs)
    override fun compare(o: SNode) = // don't consider SNodeExt equal, in order to avoid unifying DataGen (need distinct random streams)
            false //o is SNodeExt && o.hop == this.hop && o.inputs == this.inputs

    constructor(hop: Hop, vararg inputs: SNode) : this(hop, inputs.asList())

    override fun toString() = "ext(${hop.hopID} ${hop.opString})"

    override fun checkArity() {
        // no check
    }

    val hopSchema = Schema()

    // constant schema - treat like SNodeData
    init {
        assert(hop.dimsKnown()) {"dims not known for hop ${hop.hopID} ${hop.opString}"}

        if( hop.dataType == Expression.DataType.SCALAR || hop.dim1 == 1L && hop.dim2 == 1L )
        else if( hop.dim1 == 1L )
            hopSchema.put(AU.U0, hop.dim2)
        else if( hop.dim2 == 1L )
            hopSchema.put(AU.U0, hop.dim1)
        else {
            hopSchema.put(AU.U0, hop.dim1)
            hopSchema.put(AU.U1, hop.dim2)
        }

        refreshSchema()
    }

    override fun refreshSchema() {
//        // reconstruct hop based on inputs which may have changed.
//        // modifies child references of hop.
//        Spoof2Compiler.rReconstructHopDag(this, HashMap())

        // todo - think about what happens if we change the inputs of an SNodeExt
        // dg(rand) never needs change
        schema.setTo(hopSchema)
    }
}

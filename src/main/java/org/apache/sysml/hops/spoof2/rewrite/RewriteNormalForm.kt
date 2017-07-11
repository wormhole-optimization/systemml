package org.apache.sysml.hops.spoof2.rewrite

import org.apache.commons.logging.LogFactory
import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.utils.Statistics

/**
 * Applies to `sum(+)-mult(*)` when mult has no foreign parents and has >2 inputs.
 */
class RewriteNormalForm : SPlanRewriteRule() {
    companion object {
        private val LOG = LogFactory.getLog(RewriteNormalForm::class.java)!!
    }

    override fun rewriteNode(parent: SNode, node: SNode, pos: Int): RewriteResult {
        val spb = isSumProductBlock(node) ?: return RewriteResult.NoChange

        LOG.debug(spb)

        // Tracks largest sum-product statistics; see RewriteNormalForm, Statistics, AutomatedTestBase
        val thisSize = spb.names.size
        var oldLargestSize: Int
        do {
            oldLargestSize = Statistics.spoof2NormalFormNameLength.get()
        } while(thisSize > oldLargestSize && !Statistics.spoof2NormalFormNameLength.compareAndSet(oldLargestSize, thisSize))

        if( thisSize > oldLargestSize ) {
            Statistics.spoof2NormalFormAggs = spb.agg.aggreateNames.toString()
            Statistics.spoof2NormalFormInputSchemas = spb.inputSchemas.toString()
            Statistics.spoof2NormalFormChanged.set(true)
        }

        return RewriteResult.NoChange
    }

    private fun isSumProductBlock(agg: SNode): SumProductBlock? {
        if( agg is SNodeAggregate && agg.op == Hop.AggOp.SUM ) {
            val mult = agg.inputs[0]
            if( mult is SNodeNary && mult.op == SNodeNary.NaryOp.MULT
                    && mult.parents.size == 1 && mult.inputs.size > 2 ) {
                return SumProductBlock(agg)
            }
        }
        return null
    }

    private data class SumProductBlock(
            val agg: SNodeAggregate
    ) {
        val mult: SNodeNary = agg.inputs[0] as SNodeNary
        val names: List<Name> = mult.schema.names.filter(Name::isBound)
        val inputs: List<SNode> = mult.inputs
        val inputSchemas: List<Schema> = inputs.map { it.schema }
//        val inputNnz: List<Double> = inputs.map { it }

        override fun toString(): String {
            return "SumProductBlock on $agg ${agg.id}\n" +
                    "\tnames: $names aggregating ${agg.aggreateNames}\n" +
                    "\tinputSchemas: $inputSchemas"
        }
    }

//    private data class MultiplyBlock(
//            val multOp: SNodeNary.NaryOp,
//            val names: List<Name>,
//            val inputs: List<Schema>
//    )
}
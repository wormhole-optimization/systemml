package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.Hop.AggOp
import org.apache.sysml.hops.LiteralOp
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.plan.SNodeNary.NaryOp
import org.apache.sysml.parser.Expression

class RewritePushAggIntoPlus(
        val constantAggToMultiply: Boolean = false
) : SPlanRewriteRule() {

    override fun rewriteNode(parent: SNode, node: SNode, inputPosition: Int): RewriteResult {
        if (node is SNodeAggregate && node.op == AggOp.SUM
                && node.inputs[0] is SNodeNary
                && (node.inputs[0] as SNodeNary).op == NaryOp.PLUS) {
            val agg = node
            var plus = node.inputs[0] as SNodeNary

            // split CSE
            if( plus.parents.size > 1 ) {
                val copy = plus.shallowCopyNoParentsYesInputs()
                plus.parents -= agg
                agg.input = copy
                copy.parents += agg
                plus = copy
            }

            plus.inputs.mapInPlace { plusInput ->
                plusInput.parents -= plus
                agg.input = plusInput
                val copy = agg.shallowCopyNoParentsYesInputs()
                copy.parents += plus
                copy
            }
            plus.parents -= agg
            agg.parents.forEach { it.inputs[it.inputs.indexOf(agg)] = plus; plus.parents += it }
            plus.refreshSchema()

            plus.inputs.indices.forEach { checkConstantAggMult(plus.inputs[it] as SNodeAggregate) }

            if( SPlanRewriteRule.LOG.isDebugEnabled )
                SPlanRewriteRule.LOG.debug("RewritePushAggIntoPlus on (${agg.id}) $agg ${agg.schema} - (${plus.id}) $plus")
            return RewriteResult.NewNode(plus)
        } else if(node is SNodeAggregate && node.op == AggOp.SUM) {
            checkConstantAggMult(node)
        }
        return RewriteResult.NoChange
    }

    private fun checkConstantAggMult(agg: SNodeAggregate) {
        val mult = agg.input
        if( mult is SNodeNary && mult.op == NaryOp.MULT ) {
            var needsSplitCSE = mult.parents.size > 1
            val notInInput = agg.aggsNotInInputSchema()
            @Suppress("UNCHECKED_CAST")
            val litInputs = (mult.inputs.filter { it is SNodeData && it.isLiteralNumeric } as List<SNodeData>).toMutableList()

            loop@while( notInInput.isNotEmpty() && litInputs.isNotEmpty() ) {
                for( v in 1L until (1L shl notInInput.size) ) {
                    val selectSchema = notInInput.entries.filterIndexed { p, _ ->
                        v and (1L shl p) != 0L
                    }.run { Schema(this.map { (n,s) -> n to s }) }
                    val tgt = selectSchema.shapes.fold(1.0, Double::div)
                    val exact = litInputs.find {
                        val hop = it.hop as LiteralOp
                        hop.doubleValue == tgt
                    }
                    if( exact != null ) {
                        if( needsSplitCSE ) {
                            val otherParents = mult.parents.filter { it != agg }.toSet()
                            otherParents.forEach { op ->
                                val copy = mult.shallowCopyNoParentsYesInputs()
                                op.inputs.mapInPlace { opi ->
                                    if( opi == mult ) {
                                        mult.parents -= op
                                        copy.parents += op
                                        copy
                                    } else opi
                                }
                            }
                            needsSplitCSE = false
                        }
                        // exact match with a literal - eliminate the literal
                        exact.parents -= mult
                        mult.inputs -= exact
                        agg.aggs -= selectSchema
                        notInInput -= selectSchema
                        litInputs -= exact
                        // eliminate the mult if it has a single input
                        if( mult.inputs.size == 1 ) {
                            val i = mult.inputs[0]
                            i.parents -= mult
                            i.parents += agg
                            agg.input = i
                        }
                        continue@loop
                    }
                }
                break
            }
            if( constantAggToMultiply && notInInput.isNotEmpty() ) {
                val mFactor = notInInput.shapes.fold(1L, Long::times)
                val lit = SNodeData(LiteralOp(mFactor))

                mult.inputs += lit
                lit.parents += mult
                agg.aggs -= notInInput
            }
        }

    }

}

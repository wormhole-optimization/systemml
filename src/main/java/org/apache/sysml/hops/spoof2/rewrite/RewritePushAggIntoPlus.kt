package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.Hop.AggOp
import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.SNodeAggregate
import org.apache.sysml.hops.spoof2.plan.SNodeNary
import org.apache.sysml.hops.spoof2.plan.SNodeNary.NaryOp
import org.apache.sysml.hops.spoof2.plan.mapInPlace

class RewritePushAggIntoPlus : SPlanRewriteRule() {
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

            if( SPlanRewriteRule.LOG.isDebugEnabled )
                SPlanRewriteRule.LOG.debug("RewritePushAggIntoPlus on (${agg.id}) $agg ${agg.schema} - (${plus.id}) $plus")
            return RewriteResult.NewNode(plus)
        }
        return RewriteResult.NoChange
    }

}

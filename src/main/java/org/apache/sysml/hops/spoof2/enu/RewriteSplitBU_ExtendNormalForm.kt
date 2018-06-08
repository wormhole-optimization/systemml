package org.apache.sysml.hops.spoof2.enu
//
//import org.apache.sysml.hops.spoof2.plan.*
//import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriteRule
//
///**
// * Run before the normal form rewrite in order to move binds out of the way by copying the expressions below them.
// * Then use RewriteBindUnify to unify the renamed copied nodes.
// */
//class RewriteSplitBU_ExtendNormalForm : SPlanRewriteRule() {
//
//    override fun rewriteNode(parent: SNode, node: SNode, inputPosition: Int, allRoots: List<SNode>): RewriteResult {
//        if( !SumProduct.isSumProductBlock(node) )
//            return RewriteResult.NoChange
//        val cnt = splitForConstructBlock(node, parent)
//        if( LOG.isTraceEnabled && cnt > 0 )
//            LOG.trace("RewriteSplitBU_ExtendNormalForm: Copied underneath $cnt bind-unbinds blocking sum-product block expansion at node (${node.id}) $node")
//        return if( cnt == 0 ) RewriteResult.NoChange else RewriteResult.NewNode(node)
//    }
//
//    private fun splitForConstructBlock(node: SNode, parent: SNode): Int {
//        return splitForConstructBlock(node, parent, true)
//    }
//
//    private fun splitForConstructBlock(_top: SNode, _topParent: SNode, first: Boolean): Int {
//        var thisSplits = 0
//        var top = _top
//        if( !first ) {
//            top = splitBindBelowAgg(_top, _topParent)
//            if( top != _top )
//                thisSplits++
//        }
////        var topParent = _topParent
//        while (top is SNodeAggregate) {
////            topParent = top
//            top = top.input
//        }
//        return top.inputs.sumBy { child ->
//            splitForConstructBlock(child, top, false)
//        } + thisSplits
//    }
//
//    private fun splitBindBelowAgg(top: SNode, aboveTop: SNode): SNode {
//        val (bind, aboveBind) = SumProduct.getBelowAgg(top, aboveTop)
//        if( bind is SNodeBind && bind.input is SNodeUnbind) {
//            val unbind = bind.input as SNodeUnbind
//            val below = SumProduct.getBelowAgg(unbind.input)
//            if(SumProduct.COND_PRODUCT(below)) {
//                // rename below the unbind from the unbind atts to the bind atts
//                val renaming: Map<AB, AB> = unbind.unbindings.zipIntersect(bind.bindings).values.toMap()
//                LOG.debug("renaming is $renaming on unbind input ${unbind.input} ${unbind.input.schema}")
//                val newUnbindInput = unbind.input.renameCopyDown(renaming, HashMap(renaming), null)
//                bind.parents.removeIf { it == aboveBind }
//                stripDead(bind)
//                // move aboveBind's input from bind to newUnbindInput
//                do {
//                    aboveBind.inputs[aboveBind.inputs.indexOf(bind)] = newUnbindInput
//                    newUnbindInput.parents += aboveBind
//                } while (bind in aboveBind.inputs)
//                aboveBind.refreshSchemasUpward()
//                return newUnbindInput
//            }
//        }
//        return top
//    }
//
//}
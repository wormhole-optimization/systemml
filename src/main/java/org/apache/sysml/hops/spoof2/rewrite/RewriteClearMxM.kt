package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.spoof2.plan.*

/**
 * ```
 *   \/                           \/
 *  Σ[y]    E   ->         E    +[x,z]
 *   |     /  D ->        /  D  -[a,c]
 *  +[x,y,z] /  -> +[x,y,z] /   /
 *  -[a,b,c]    -> -[a,b,c]   Σ[b]
 *   |          ->        | /
 *   C          ->        C
 * ```
 */
class RewriteClearMxM : SPlanRewriteRule() {
    override fun rewriteNode(parent: SNode, node: SNode, pos: Int): RewriteResult {
        if (node is SNodeAggregate
                && node.input is SNodeBind && node.input.inputs[0] is SNodeUnbind) {
            val agg = node
            var bind = agg.input as SNodeBind
            var unbind = bind.input as SNodeUnbind

            // Split CSEs
            if( bind.parents.size > 1 ) {
                val copy = bind.shallowCopyNoParentsYesInputs()
                bind.parents -= agg
                agg.input = copy
                copy.parents += agg
                bind = copy
            }
            if( unbind.parents.size > 1 ) {
                val copy = unbind.shallowCopyNoParentsYesInputs()
                unbind.parents -= bind
                bind.input = copy
                copy.parents += bind
                unbind = copy
            }

            // map the aggNames below the unbind-bind
            var offset = 0
            agg.aggreateNames.mapInPlace {
                if( it !in bind.bindings.values )
                    it
                else {
                    val pos = bind.bindings.entries.find { (_,n) -> n == it }!!.key
                    //remove names from unbind and bind that were aggregated away
                    val oldAggName = unbind.unbindings[pos]!!
                    bind.bindings -= pos
                    unbind.unbindings -= pos
                    val adjustPositions: (Int, Name) -> Pair<Int,Name> = { p, n -> (if( p > pos ) p-1 else p) to n }
                    bind.bindings.mapInPlace(adjustPositions)
                    unbind.unbindings.mapInPlace(adjustPositions)
                    oldAggName
                }
            }
            //wire agg to unbind.input and place bind and unbind above; dead code elim
            val aggParents = ArrayList(agg.parents)
            agg.input = unbind.input
            agg.input.parents -= unbind
            agg.input.parents += agg
            unbind.input = agg
            agg.parents.clear()
            agg.parents += unbind
            bind.parents -= agg
            aggParents.forEach { it.inputs[it.inputs.indexOf(agg)] = bind; bind.parents += it }
            // keep it simple; let RewriteBindUnify handle empty bind/unbind
//            var top: SNode
//            if( bind.bindings.isEmpty() )
//                RewriteBindElim.eliminateEmpty(bind)
//            if( unbind.unbindings.isEmpty() )
//                RewriteBindElim.eliminateEmpty(unbind)
            agg.refreshSchema()
            unbind.refreshSchema()
            bind.refreshSchema()
            if( LOG.isTraceEnabled )
                LOG.trace("RewriteClearMxM: pull unbind/bind above (${agg.id}) $agg")
            return RewriteResult.NewNode(bind)
        }
        return RewriteResult.NoChange
    }

}
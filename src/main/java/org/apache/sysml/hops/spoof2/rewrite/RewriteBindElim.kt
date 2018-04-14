package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.spoof2.plan.agBindings
import org.apache.sysml.hops.spoof2.plan.*

/**
 * Eliminate pairs of Bind-Unbind.
 *
 * 0. If a Bind or Unbind is empty, eliminate it.
 * 0. Combine consecutive Binds/Unbinds when the child has no foreign parents.
 * 0. If at least two parents are Binds (or Unbinds) and they contain some of the same mappings,
 *    then move the common mappings into a common SNode(Un)Bind and rewire.
 * 1. Bind-Unbind, when Unbind has no foreign parents.
 *    Rename Unbound names to Bound names, recursively downwards.
 *    Do this for as many Unbound names as possible. Eliminate the Unbound/Bound if they become empty.
 * 2. Unbind-Bind, when Bind has no foreign parents. Eliminate names in identical positions.
 */
class RewriteBindElim : SPlanRewriteRule() {
    companion object {
        private fun canEliminateEmpty(node: SNode) =
                node is SNodeBind && node.bindings.isEmpty()
                        || node is SNodeUnbind && node.unbindings.isEmpty()

        fun eliminateNode(node: SNode): SNode {
            val child = node.inputs[0]
            SNodeRewriteUtils.removeAllChildReferences(node) // clear node.inputs, remove node from child.parents
            SNodeRewriteUtils.rewireAllParentChildReferences(node, child) // for each parent of node, change its input from node to child and add the parent to child
            return child
        }
    }

    override fun rewriteNode(parent: SNode, node: SNode, inputPosition: Int, allRoots: List<SNode>): RewriteResult {
        return rRewriteNode(parent, node, false)
    }
    private tailrec fun rRewriteNode(parent: SNode, node: SNode, changed: Boolean): RewriteResult {
        if( canEliminateEmpty(node) ) {
            if (SPlanRewriteRule.LOG.isDebugEnabled)
                SPlanRewriteRule.LOG.debug("RewriteBindElim on empty ${node.id} $node.")
            return rRewriteNode(parent, eliminateNode(node), true)
        }
//        if( node.visited || parent.visited ) // safety; try removing this later
//            return if (changed) RewriteResult.NewNode(node) else RewriteResult.NoChange
        // DISABLED combine common mappings.
        // Defer to CSE Elim if the mappings are identical. Otherwise if not identical, don't combine.
//        if( parent is SNodeBind || parent is SNodeUnbind ) {
//            // try to find another parent that is the same type and has overlapping bindings
//            val parent2 = node.parents.find { np -> np !== parent && np.javaClass == parent.javaClass && parent.agBindings().any { (dim,n) -> np.agBindings()[dim] == n } }
//            if( parent2 != null && !parent2.visited ) {
//                val commonBindings = parent.agBindings().intersectEntries(parent2.agBindings())
//                node.parents.remove(parent)
//                node.parents.remove(parent2)
//                val newBind =
//                        if( parent is SNodeBind ) SNodeBind(node, commonBindings)
//                        else SNodeUnbind(node, commonBindings)
////                newBind.visited = node.visited
//                parent.inputs[0] = newBind
//                parent2.inputs[0] = newBind
//                newBind.parents += parent
//                newBind.parents += parent2
//                parent.agBindings() -= commonBindings.keys   // could create an empty Bind/Unbind in the parent; need another pass
//                parent2.agBindings() -= commonBindings.keys
//                if (SPlanRewriteRule.LOG.isDebugEnabled)
//                    SPlanRewriteRule.LOG.debug("RewriteBindElim combine common mappings of ${node.id}'s parents " +
//                            "${parent.id} and ${parent2.id} into new ${newBind.id} $newBind.")
//                return rRewriteNode(parent, newBind, true)
//            }
//        }
        // bind-bind or unbind-unbind; no foreign parents
        if(     (node is SNodeBind && node.inputs[0] is SNodeBind
                    || node is SNodeUnbind && node.inputs[0] is SNodeUnbind)
                && node.inputs[0].parents.size == 1 ) {
            val child = node.inputs[0]
            node.check(node.agBindings().keys != child.agBindings().keys) {"Overlap between keys of consecutive ${node.id} $node $child"}
            node.agBindings() += child.agBindings()

            eliminateNode(child)

            if (SPlanRewriteRule.LOG.isDebugEnabled)
                SPlanRewriteRule.LOG.debug("RewriteBindElim on consecutve Unbinds at ${node.id} to $node.")
            return rRewriteNode(parent, node, true)
        }
        if( node is SNodeBind ) {
            val bind = node
            // bind-unbind
            if( bind.inputs[0] is SNodeUnbind && bind.inputs[0].parents.size == 1 ) {
                val unbind = bind.inputs[0] as SNodeUnbind
                val renamings = mutableMapOf<AB,AB>()
                val iter = bind.bindings.iterator()
                while( iter.hasNext() ) {
                    val (dim,newName) = iter.next()
                    if( dim in unbind.unbindings ) {
                        // this dim is unbound and then bound. Rename the unbound name to the bound name.
                        val oldName = unbind.unbindings.remove(dim)!!
                        iter.remove()
                        renamings += oldName to newName
                    }
                }
                if( renamings.isNotEmpty() ) {
                    val unbindChild = unbind.inputs[0]
                    unbindChild.renameAttributes(renamings, false)
                    if (SPlanRewriteRule.LOG.isDebugEnabled)
                        SPlanRewriteRule.LOG.debug("RewriteBindElim Bind(${bind.id})-Unbind(${unbind.id}): " +
                                "rename sub-tree of Unbind by $renamings" +
                                (if(bind.bindings.isEmpty()) " and elim Bind" else "") +
                                if(unbind.unbindings.isEmpty()) " and elim Unbind" else "")

                    // Common case: the resulting bind-unbind is empty.
                    if (unbind.unbindings.isEmpty()) eliminateNode(unbind)
                    return if (bind.bindings.isEmpty())
                        rRewriteNode(parent, eliminateNode(bind), true)
                    else RewriteResult.NewNode(bind)
                }
            }
        }
        if( node is SNodeUnbind ) {
            val unbind = node
            // unbind-bind
            if( unbind.inputs[0] is SNodeBind && unbind.inputs[0].parents.size == 1 ) {
                val bind = node.inputs[0] as SNodeBind
                // elminate unbindings and bindings where the names are in the same position
                val iter = unbind.unbindings.iterator()
                var numRemoved = 0
                while( iter.hasNext() ) {
                    val (dim,unboundName) = iter.next()
                    if( unboundName == bind.bindings[dim] ) {
                        bind.bindings.remove(dim)
                        iter.remove()
                        numRemoved++
                    }
                }
                if (numRemoved > 0) {
                    if (SPlanRewriteRule.LOG.isDebugEnabled)
                        SPlanRewriteRule.LOG.debug("RewriteBindElim Unbind(${unbind.id})-Bind(${bind.id}) " +
                                "to $unbind and $bind, removing $numRemoved names" +
                                (if(unbind.unbindings.isEmpty()) " and elim Unbind" else "" +
                                        if(bind.bindings.isEmpty()) " and elim Bind" else ""))

                    // Common case: the resulting unbind-bind is empty.
                    if (bind.bindings.isEmpty()) eliminateNode(bind)
                    return if (unbind.unbindings.isEmpty())
                        rRewriteNode(parent, eliminateNode(unbind), true)
                    else RewriteResult.NewNode(unbind)
                }
            }
        }
        return if (changed) RewriteResult.NewNode(node) else RewriteResult.NoChange
    }

}

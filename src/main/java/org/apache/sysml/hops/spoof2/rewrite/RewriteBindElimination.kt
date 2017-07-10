package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.spoof2.plan.*

/**
 * Eliminate pairs of Bind-Unbind.
 *
 * 0. If a Bind or Unbind is empty, eliminate it.
 * 0. Combine consecutive Binds/Unbinds when the child has no foreign parents.
 * 0. If at least two parents are Binds (or Unbinds) and they contain some of the same mappings,
 *    then move the common mappings into a common SNodeBind and rewire.
 * 1. Bind-Unbind, when Unbind has no foreign parents.
 *    Rename Unbound names to Bound names, recursively downwards.
 *    Do this for as many Unbound names as possible. Eliminate the Unbound/Bound if they become empty.
 * 2. Unbind-Bind, when Bind has no foreign parents. Eliminate names in identical positions.
 */
class RewriteBindElimination : SPlanRewriteRule() {
    private fun canEliminateEmpty(node: SNode) =
            node is SNodeBind && node.bindings.isEmpty()
            || node is SNodeUnbind && node.unbindings.isEmpty()

    private fun eliminateEmpty(node: SNode): SNode {
        val child = node.inputs[0]
        SNodeRewriteUtils.removeAllChildReferences(node) // clear node.inputs, child.parents
        SNodeRewriteUtils.rewireAllParentChildReferences(node, child) // for each parent of node, change its input from node to child and add the parent to child
        return child
    }

    /** "Agnostic bindings", for SNodeBind or SNodeUnbind. */
    private val SNode.agbindings: MutableMap<Int, String>
        get() = when(this) {
            is SNodeBind -> this.bindings
            is SNodeUnbind -> this.unbindings
            else -> throw IllegalArgumentException()
        }

    override tailrec fun rewriteNode(parent: SNode, node: SNode, pos: Int): SNode {
        if( canEliminateEmpty(node) ) {
            if (SPlanRewriteRule.LOG.isDebugEnabled)
                SPlanRewriteRule.LOG.debug("RewriteBindElimination on empty ${node.id} $node.")
            return rewriteNode(parent, eliminateEmpty(node), pos)
        }
        if( parent is SNodeBind || parent is SNodeUnbind ) {
            // try to find another parent that is the same type and has overlapping bindings
            val parent2 = node.parents.find { np -> np !== parent && np.javaClass == parent.javaClass && parent.agbindings.any { (dim,n) -> np.agbindings[dim] == n } }
            if( parent2 != null ) {
                val commonBindings = parent.agbindings.intersectEntries(parent2.agbindings)
                node.parents.remove(parent)
                node.parents.remove(parent2)
                val newBind = SNodeBind(node, commonBindings)
                parent.inputs[0] = newBind
                parent2.inputs[0] = newBind
                newBind.parents += parent
                newBind.parents += parent2
                parent.agbindings -= commonBindings.keys   // could create an empty Bind/Unbind in the parent; need another pass
                parent2.agbindings -= commonBindings.keys
                if (SPlanRewriteRule.LOG.isDebugEnabled)
                    SPlanRewriteRule.LOG.debug("RewriteBindElimination combine common mappings of parents " +
                            "${parent.id} and ${parent2.id} into new ${newBind.id} $newBind.")
                return rewriteNode(parent, newBind, pos)
            }
        }
        // bind-bind or unbind-unbind; no foreign parents
        if(     (node is SNodeBind && node.inputs[0] is SNodeBind
                    || node is SNodeUnbind && node.inputs[0] is SNodeUnbind)
                && node.inputs[0].parents.size == 1 ) {
            val child = node.inputs[0]
            node.check(node.agbindings.keys != child.agbindings.keys) {"Overlap between keys of consecutive ${node.id} $node $child"}
            node.agbindings += child.agbindings

            eliminateEmpty(child)

            if (SPlanRewriteRule.LOG.isDebugEnabled)
                SPlanRewriteRule.LOG.debug("RewriteBindElimination on consecutve Unbinds at ${node.id} to $node.")
            return rewriteNode(parent, node, pos)
        }
        if( node is SNodeBind ) {
            val bind = node
            // bind-unbind
            if( bind.inputs[0] is SNodeUnbind && bind.inputs[0].parents.size == 1 ) {
                val unbind = node.inputs[0] as SNodeUnbind
                val renamings = mutableMapOf<Name,Name>()
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
                        SPlanRewriteRule.LOG.debug("RewriteBindElimination Bind-Unbind: " +
                                "rename sub-tree of Unbind ${unbind.id} by $renamings")

                    // Common case: the resulting bind-unbind is empty.
                    val child2 = if (unbind.unbindings.isEmpty()) eliminateEmpty(unbind) else unbind
                    return if (bind.bindings.isEmpty())
                        rewriteNode(parent, eliminateEmpty(bind), pos)
                    else bind
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
                        SPlanRewriteRule.LOG.debug("RewriteBindElimination Unbind-Bind on Unbind ${unbind.id} to $unbind and $bind, removing $numRemoved names")

                    // Common case: the resulting unbind-bind is empty.
                    val child2 = if (bind.bindings.isEmpty()) eliminateEmpty(bind) else bind
                    return if (unbind.unbindings.isEmpty())
                        rewriteNode(parent, eliminateEmpty(unbind), pos)
                    else unbind
                }
            }
        }
        return node
    }

}

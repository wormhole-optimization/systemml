package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.spoof2.plan.*

/**
 * Eliminate pairs of Bind-Unbind.
 *
 * 0. If a Bind or Unbind is empty, eliminate it.
 * 0. Combine consecutive Binds/Unbinds when the child has no foreign parents.
 * 1. Bind-Unbind, when Unbind has no foreign parents.
 *    Rename Unbound names to Bound names, recursively downwards.
 *    Do this for as many Unbound names as possible. Eliminate the Unbound/Bound if they become empty.
 * 2. Unbind-Bind, when Bind has no foreign parents. Similar to 1.
 */
class RewriteBindElimination : SPlanRewriteRule() {
    private fun canEliminateEmpty(node: SNode) =
            node is SNodeBind && node.bindings.isEmpty()
            || node is SNodeUnbind && node.unbinding.isEmpty()

    private fun eliminateEmpty(parent: SNode, node: SNode, pos: Int): SNode {
        val child = node.inputs[0]
        SNodeRewriteUtils.removeAllChildReferences(node)
        SNodeRewriteUtils.rewireAllParentChildReferences(node, child)
//        SNodeRewriteUtils.replaceChildReference(parent, node, child)
        if (SPlanRewriteRule.LOG.isDebugEnabled)
            SPlanRewriteRule.LOG.debug("Applied RewriteBindElimination on empty ${node.id} $node.")
        return child
    }

    override fun rewriteNode(parent: SNode, node: SNode, pos: Int): SNode {

        if( canEliminateEmpty(node) )
            return eliminateEmpty(parent, node, pos)
        else if( node is SNodeBind && node.inputs[0] is SNodeUnbind && node.inputs[0].parents.size == 1 ) {
            val bind = node
            val unbind = node.inputs[0] as SNodeUnbind
            val renamings = mutableMapOf<Name,Name>()
            val iter = bind.bindings.iterator()
            while( iter.hasNext() ) {
                val (dim,newName) = iter.next()
                if( dim in unbind.unbinding ) {
                    // this dim is unbound and then bound. Rename the unbound name to the bound name.
                    val oldName = unbind.unbinding.remove(dim)!!
                    iter.remove()
                    renamings += oldName to newName
                }
            }
            val unbindChild = unbind.inputs[0]
            unbindChild.renameAttributes(renamings, false)

            if (SPlanRewriteRule.LOG.isDebugEnabled)
                SPlanRewriteRule.LOG.debug("Applied RewriteBindElimination Bind-Unbind: " +
                        "rename sub-tree of Unbind ${unbind.id} by $renamings")

            val child2 = if(unbind.unbinding.isEmpty()) eliminateEmpty(bind, unbind, 0) else unbind
            val child1 = if(bind.bindings.isEmpty())    eliminateEmpty(parent, bind, 0) else bind
            return child1
        }

        return node
    }

}

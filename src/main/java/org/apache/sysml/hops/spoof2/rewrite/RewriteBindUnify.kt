package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriteRule.RewriteResult
import org.apache.sysml.hops.spoof2.plan.agBindings
import java.util.*

/**
 * 0. Eliminate empty bind/unbind.
 *
 * 1. For Bind-Unbind and Unbind-Bind pairs that match on part of their schema
 * ```
 *  Z     ->
 *  |  F' ->     F'
 * -a /   ->     |
 * +a     -> Z  +a
 *  |     -> | /
 *  A     -> A
 * ```
 * The `+a` is `node` and the `-a` is above.
 *
 * 2. Given the pattern
 * ```
 * +a  +b
 *  \ /
 *   A
 * ```
 * attempt to change the `b` to `a` for the operation above `b`.
 * Suppose `X` has `a` in its schema and `Y` does not.
 * Suppose `C` has `b` in its schema and `D` does not.
 * Perform the following:
 * ```
 *                         Z
 *                         |
 *                        +b
 *         Z    ->        -a
 *         |    ->         |
 *  W  X   Y    ->  X  W   Y
 *  |  | / | \  ->  |  | / | \
 * +a  +b  C  D -> +b  +a +a  D
 *  \ /         ->  \ /   -b
 *   A          ->   A     |
 *                         C
 * ```
 *
 * 3.
 * Suppose `X` has `a` in its schema and `Y` does not.
 * Suppose `C` has `b` in its schema and `D` does not.
 * ```
 *                           Z
 *         Z     ->          |
 *         |     ->         +b
 *     X   Y     ->     X   -a
 * F   | / | \   -> F   |    |
 *  \ +b   C  D  ->  \ +b    Y
 *    -a         ->    -a  / | \
 *     |         ->     | / +a  D
 *     A         ->     A   -b
 *                           |
 *                           C
 * ```
 *
 */
class RewriteBindUnify : SPlanRewriteRuleBottomUp() {

    companion object {
        private fun SNode.isBindOrUnbind() = this is SNodeBind || this is SNodeUnbind
    }

    override fun rewriteNodeUp(node: SNode): RewriteResult {
        return rRewriteBindUnify(node, false)
    }
    private tailrec fun rRewriteBindUnify(node: SNode, changed: Boolean): RewriteResult {
        if( node.isBindOrUnbind() ) {
            // empty bind/unbind
            if( node.agBindings().isEmpty() ) {
                val child = RewriteBindElim.eliminateEmpty(node)
                child.visited = false
                if( LOG.isTraceEnabled )
                    LOG.trace("RewriteBindUnify: on empty ${node.id} $node; replace with child ${child.id} $child")
                return rRewriteBindUnify(child, true)
            }

            // bind-bind or unbind-unbind: combine together.
            // Split CSE if lower one has a foreign parent.
            if( node.parents.any { it.javaClass == node.javaClass } ) {
//            if( node.parents.size == 1 && node.parents[0].javaClass == node.javaClass ) { // Use this version to disable CSE splitting
                val killParent = if( node.parents.size == 1 ) {
                    node.agBindings() += node.parents[0].agBindings()
                    node.refreshSchema()
                    node.parents[0]
                } else {
                    val matchingParent = node.parents.first { it.javaClass == node.javaClass }
                    val newBind = node.shallowCopyNoParentsYesInputs()
                    newBind.agBindings() += matchingParent.agBindings()
                    newBind.refreshSchema()
                    matchingParent.inputs[0] = newBind
                    node.parents -= matchingParent
                    matchingParent
                }
                RewriteBindElim.eliminateEmpty(killParent)
                if( LOG.isTraceEnabled )
                    LOG.trace("RewriteBindUnify: combine consecutive ${killParent.id} -- ${node.id} to $node ${node.schema}")
                return rRewriteBindUnify(node, true)
            }


            // bind-unbind or unbind-bind with common bindings -- eliminate the common ones
            // Split CSE if foreign parent present on node.
            val above = node.parents.find { it.isBindOrUnbind() && it.javaClass != node.javaClass
                    && it.agBindings().any { (p,n) -> node.agBindings()[p] == n }
            }
            if( above != null ) {
                val commonBindings = node.agBindings().intersectEntries(above.agBindings())
                // Safe to elim if the bottom is unbind OR if the bottom is bind and the unbind does not change name positions
                if( node is SNodeBind || commonBindings.none { (p,n) -> node.schema.names[p] != n } ) {
                    // above can only be a parent once because it is a bind/unbind
                    val otherNodeParents = node.parents.filter { it !== above }
                    if (otherNodeParents.isNotEmpty()) {
                        // Split CSE: connect otherNodeParents to a copy of node
                        val copy = node.shallowCopyNoParentsYesInputs()
                        otherNodeParents.forEach {
                            it.inputs[it.inputs.indexOf(node)] = copy
                            copy.parents += it
                            node.parents -= it
                        }
                    }
                    // only parent of node is above
                    assert(node.parents.size == 1)
                    commonBindings.forEach { (k, _) ->
                        node.agBindings() -= k
                        above.agBindings() -= k
                    }
                    node.refreshSchema()
                    // Be careful!
                    val tmp = above.refreshSchemasUpward() // insidious situation: The unbind in unbind-bind shifts the indices

                    if (above.agBindings().isEmpty())
                        RewriteBindElim.eliminateEmpty(above)
                    val newNode = if (node.agBindings().isEmpty()) RewriteBindElim.eliminateEmpty(node) else node
                    if (LOG.isTraceEnabled)
                        LOG.trace("RewriteBindUnify: elim redundant bindings $commonBindings in ${above.id} $above -- ${node.id} $node ${if (otherNodeParents.isNotEmpty()) "(with split CSE)" else ""}")
                    return rRewriteBindUnify(newNode, true)
                }
            }
        }

        if( node is SNodeUnbind ) {
            // unbind-bind with different bindings - try to unify
            val above = node.parents.find { it is SNodeBind && !it.bindings.keys.disjoint(node.unbindings.keys) }
            if( above != null ) {
                above as SNodeBind
                for (unbindBindPos in node.unbindings.keys
                        .intersect(above.bindings.keys)
                        .filter { node.unbindings[it]!! != above.bindings[it]!! }) {
                    // if aboveName < nodeName, then rename aboveName to nodeName and propagate up
                    // if nodeName < aboveName, then rename nodeName to aboveName and propagate down
                    val aboveName = above.bindings[unbindBindPos]!!
                    val nodeName = node.unbindings[unbindBindPos]!!
                    val success = if( Schema.nameComparator.compare(aboveName, nodeName) < 0 )
                        tryRenameSingle(above, aboveName, nodeName)
                    else
                        tryRenameSingle(node, nodeName, aboveName)
                    if( success )
                        return rRewriteBindUnify(node, true)
                }
            }
        }

        // check if two parents have a Bind to the same dimension. If so, try to unify them.
        val bindIndices = node.parents.withIndex().filter { (_,p) -> p is SNodeBind }.map { (i,_) -> i }
        for( bindi in 0..bindIndices.size-2) {
            val bind1 = node.parents[bindIndices[bindi]] as SNodeBind
            for( bindj in bindi+1..bindIndices.size-1) {
                // see if there is overlap. If so, try renaming the bindj to bindi
                val bind2 = node.parents[bindIndices[bindj]] as SNodeBind
                // Common positions that map to different names
                for( bindingPosition in bind1.bindings.keys
                        .intersect(bind2.bindings.keys)
                        .filter { bind1.bindings[it]!! != bind2.bindings[it]!! }) {
                    val name1 = bind1.bindings[bindingPosition]!!
                    val name2 = bind2.bindings[bindingPosition]!!
                    val success = if( Schema.nameComparator.compare(name1, name2) < 0 )
                        tryRenameSingle(bind1, name1, name2)
                    else
                        tryRenameSingle(bind2, name2, name1)
                    if( success )
                        return rRewriteBindUnify(node, true)
                }
            }
        }

        return if (changed) RewriteResult.NewNode(node) else RewriteResult.NoChange
    }

    /**
     * Try to rename [oldName] to [newName] in [node]. If successful, propagate the renaming.
     *
     * If [node] is [SNodeBind], it is successful if at least one parent of [node] does not have [newName] in its schema,
     * and the propagation is upward.
     * If [node] is [SNodeUnbind], it is successful if [node]'s input does not have [newName] in its schema,
     * and the propagation is downward.
     */
    private fun tryRenameSingle(node: SNode, oldName: Name, newName: Name): Boolean {
        assert( oldName != newName )
        assert( node.isBindOrUnbind() )

        if( node is SNodeUnbind ) {
            if( newName !in node.input.schema ) {
                val bindingPosition = node.unbindings.entries.find { (_,n) -> n == oldName }!!.key
                node.unbindings.mapValuesInPlace { if( it == oldName ) newName else it }
                rRenamePropagate(oldName, newName, node.input, node)
                if( oldName[0] != newName[0] )
                    node.refreshSchemasUpward()
                if (LOG.isTraceEnabled)
                    LOG.trace("RewriteBindUnify: downward propagate rename $bindingPosition: $oldName -> $newName on ${node.id}")
                return true
            }
        } else {
            node as SNodeBind
            val (bind2parentsOverlap, bind2parentsNoOverlap) = node.parents.partition { newName in it.schema }
            if (bind2parentsNoOverlap.isNotEmpty()) {
                val bindingPosition = node.bindings.entries.find { (_, n) -> n == oldName }!!.key
                // Create new bind on this position to the new name:
                // bind2parentParents -> Bind[oldName] -> Unbind[newName] -> bind2parent -> Bind[newName] -> node

                // Use existing Bind[newName] if possible
                val belowBind = node.input
                val newBindings = node.bindings + mapOf(bindingPosition to newName)
                val bindNewName = belowBind.parents.find {
                    it !== node && it is SNodeBind &&
                            it.bindings == newBindings
                } ?: if (bind2parentsOverlap.isEmpty()) {
                    // safe to do a destructive rename
                    node.bindings[bindingPosition] = newName
                    node.refreshSchema()
                    node
                } else SNodeBind(belowBind, newBindings).apply { this.visited = belowBind.visited }

                if (node !== bindNewName) {
                    bind2parentsNoOverlap.forEach { bind2parent ->
                        bind2parent.inputs[bind2parent.inputs.indexOf(node)] = bindNewName
                        bindNewName.parents += bind2parent
                        node.parents -= bind2parent
                    }
                    if (node.parents.isEmpty()) // eliminate bind (dead code)
                        belowBind.parents -= node
                }

                bind2parentsNoOverlap.toSet().forEach {
                    if( newName !in it.schema ) // we may handle a parent in the middle of rRenamePropagate
                        rRenamePropagate(oldName, newName, it, bindNewName)
                }

                if (LOG.isTraceEnabled)
                    LOG.trace("RewriteBindUnify: upward propagate rename $bindingPosition: $oldName -> $newName on ${node.id} above ${belowBind.id}, starting with ${bindNewName.id}")
                return true
            }
        }
        return false
    }

    private fun rRenamePropagate(oldName: Name, newName: Name, node: SNode, fromNode: SNode) {
        val refreshParentsList = LinkedList<SNode>()
        rRenamePropagate(oldName, newName, node, fromNode, refreshParentsList)
        refreshParentsList.forEach { n -> n.parents.toSet().forEach {
            if(oldName in it.schema || (it is SNodeUnbind && oldName in it.unbindings.values) || it is SNodeAggregate && oldName in it.aggreateNames)
                rRenamePropagate(oldName, newName, it, n)
        } }
    }

    /**
     * Propagate the name change from [oldName] to [newName] throughout the DAG.
     * The initial call to this method is on the first [node] on which the renaming is to occur
     * and is initiated from [fromNode], which is either a parent or child of [node].
     *
     * Stop Condition 1:
     * If [newName] is in [node]'s schema, then we cannot do the rename here; either
     * (a) if [fromNode] is a child of [node], then replace the input leading to [fromNode] as
     *     `node -> Bind[oldName] -> Unbind[newName] -> fromNode`, or
     * (b) if [fromNode] is a parent of [node], then replace the parent leading to [fromNode] as
     *     `fromNode -> Bind[newName] -> Unbind[oldName] -> node`.
     *
     * Stop Condition 2:
     * * If we reach an [SNodeAggregate] whose aggregate names include [oldName], then change it to [newName] and stop.
     *   (We must have entered the agg from below, because [oldName] is not in scope above the agg.)
     * * If we reach an [SNodeUnbind] that unbinds [oldName], then change it to unbinding [newName] and stop.
     *   (We must have entered the unbind from below because [oldName] is not in scope above the agg.)
     * * If we reach an [SNodeBind] that binds [oldName], then change it to binding [newName] and stop.
     *   (We must have entered the bind from above because [oldName] is not in scope below the bind.)
     *   **But continue with bind's other parents!**
     *
     * If we do not meet a stopping condition, then continue the propagation.
     * Include inputs that have [oldName] in its schema.
     * Include all parents.
     * Exclude [fromNode].
     *
     * @param refreshParentsList A list of nodes whose parents should be checked for propagation after the recursion finishes
     */
    private fun rRenamePropagate(oldName: Name, newName: Name, node: SNode, fromNode: SNode, refreshParentsList: MutableList<SNode>) {
//        LOG.trace("at (${node.id}) $node")
        val fromInput = fromNode in node.inputs
        // Stop on Name Conflict.
        if( newName in node.schema ) {
            if( fromInput ) {
                val bindingPosition = fromNode.schema.names.indexOf(newName)
                val unbindNew = SNodeUnbind(fromNode, mapOf(bindingPosition to newName)).apply { this.visited = fromNode.visited }
                val bindOld = SNodeBind(unbindNew, mapOf(bindingPosition to oldName)).apply { this.visited = fromNode.visited }
                node.inputs.mapInPlace {
                    if (it == fromNode) {
                        fromNode.parents -= node
                        bindOld.parents += node
                        bindOld
                    } else it
                }
            } else {
                val bindingPosition = node.schema.names.indexOf(newName)
                val unbindOld = SNodeUnbind(node, mapOf(bindingPosition to oldName))
                val bindNew = SNodeBind(unbindOld, mapOf(bindingPosition to newName))
                fromNode.inputs.mapInPlace {
                    if( it == node ) {
                        node.parents -= fromNode
                        bindNew.parents += fromNode
                        bindNew
                    } else it
                }
            }
            return
        }
        // Stop when closing the scope of oldName via Agg or Unbind. (These have a single input.)
        when( node ) {
            is SNodeAggregate -> {
                if( oldName in node.aggreateNames ) {
                    node.aggreateNames[node.aggreateNames.indexOf(oldName)] = newName
                    return
                }
            }
            is SNodeUnbind -> {
                if( oldName in node.unbindings.values ) {
                    node.unbindings.mapValuesInPlace { if( it == oldName ) newName else it }
                    if( oldName[0] != newName[0] )
                        node.refreshSchemasUpward()
                    return
                }
            }
            is SNodeBind -> {
                if( oldName in node.bindings.values ) {
                    node.bindings.mapValuesInPlace { if( it == oldName ) newName else it }
                    node.refreshSchema()
                    // refresh the parents of SNodeBind after the recursion finishes
                    if( node.parents.size > 1 )
                        refreshParentsList += node
                    return
                }
            }
        }
        // for each input to node, if it has oldName in its schema, add a Bind[newName] -> Unbind[oldName] -> child
        node.inputs.toSet().forEach { nodeInput ->
            if (nodeInput != fromNode && oldName in nodeInput.schema) {
                rRenamePropagate(oldName, newName, nodeInput, node, refreshParentsList)
            }
        }
        node.refreshSchema()
        // Recurse to renaming parents above
        node.parents.toSet().forEach {
            if( it != fromNode && (oldName in it.schema || it is SNodeUnbind && oldName in it.unbindings.values) || it is SNodeAggregate && oldName in it.aggreateNames)
                rRenamePropagate(oldName, newName, it, node, refreshParentsList)
        }
    }


}

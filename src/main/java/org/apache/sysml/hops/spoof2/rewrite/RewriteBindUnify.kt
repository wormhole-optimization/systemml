package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriteRule.RewriteResult
import org.apache.sysml.hops.spoof2.plan.agBindings

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

            // bind-bind or unbind-unbind
            // Split CSE if lower one has a foreign parent
            if( node.parents.any { it.javaClass == node.javaClass } ) {
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
                val unbind = when( node ) {
                    is SNodeBind -> above
                    is SNodeUnbind -> node
                    else -> throw AssertionError()
                } as SNodeUnbind
                if( commonBindings.none { (p,n) -> unbind.input.schema.names[p] != n } ) {
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
//                    above.refreshSchemasUpward() // insidious situation: The unbind in unbind-bind shifts the indices // todo make a cleaner transpose handling

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
                for (unbindBindPos in node.unbindings.keys.intersect(above.bindings.keys)) {
                    val oldName = above.bindings[unbindBindPos]!!
                    val newName = node.unbindings[unbindBindPos]!!
                    if( tryRenameSingle(above, oldName, newName) )
                        return rRewriteBindUnify(node, true)
                }
            }
        }

        // todo - fix this pattern. Need to switch above in addition to fixing below.
//        if( node is SNodeBind ) {
//            // check for unbind parent and bind parent with same mappings // test pattern 4
//            // todo - expand this pattern toward when the binds and unbinds are split up / shared
//            val p1Unbind = node.parents.find { it is SNodeUnbind && it.unbindings.values.toSet() == node.bindings.values.toSet() } as? SNodeUnbind
//            if( p1Unbind != null ) {
//                val p2Bind = p1Unbind.parents.find { it is SNodeBind && it.bindings == p1Unbind.unbindings } as? SNodeBind
//                if( p2Bind != null ) {
//                    var res = node
//                    p2Bind.input = node.input
//                    p1Unbind.parents -= p2Bind
//                    node.input.parents += p2Bind
//                    // Dead code elim, if p1Unbind has only one parent (p2Bind)
//                    if( p1Unbind.parents.isEmpty() ) {
//                        node.parents -= p1Unbind
//                        if( node.parents.isEmpty() ) {
//                            node.input.parents -= node
//                            res = p2Bind
//                        }
//                    }
//                    if (LOG.isTraceEnabled)
//                        LOG.trace("RewriteBindUnify: eliminate transpose-like renaming pattern (${p2Bind.id}) $p2Bind -- (${p1Unbind.id}) $p1Unbind -- (${node.id}) $node")
//                    return rRewriteBindUnify(res, true)
//                }
//            }
//        }

        // check if two parents have a Bind to the same dimension. If so, try to unify them.
        val bindIndices = node.parents.withIndex().filter { (_,p) -> p is SNodeBind }.map { (i,_) -> i }
        for( bindi in 0..bindIndices.size-2) {
            val bind1 = node.parents[bindIndices[bindi]] as SNodeBind
            for( bindj in bindi+1..bindIndices.size-1) {
                // see if there is overlap. If so, try renaming the bindj to bindi
                val bind2 = node.parents[bindIndices[bindj]] as SNodeBind
                // Common positions that map to different names
                val commonBindingPositions = bind1.bindings.keys.intersect(bind2.bindings.keys).filter { bind1.bindings[it]!! != bind2.bindings[it]!! }
                if( commonBindingPositions.isNotEmpty() ) {
                    val bindingPosition = commonBindingPositions.first()
                    val newName = bind1.bindings[bindingPosition]!!
                    val oldName = bind2.bindings[bindingPosition]!!

                    if( tryRenameSingle(bind2, oldName, newName) )
                        return rRewriteBindUnify(node, true)
                }
            }
        }

        return if (changed) RewriteResult.NewNode(node) else RewriteResult.NoChange
    }

    private fun tryRenameSingle(bind: SNodeBind, oldName: Name, newName: Name): Boolean {
        if(oldName == newName)
            return false
        val (bind2parentsOverlap, bind2parentsNoOverlap) = bind.parents.partition { newName in it.schema }
        if (bind2parentsNoOverlap.isNotEmpty()) {
            val bindingPosition = bind.bindings.entries.find { (_,n) -> n == oldName }!!.key
            // Create new bind on this position to the new name:
            // bind2parentParents -> Bind[oldName] -> Unbind[newName] -> bind2parent -> Bind[newName] -> node

            // Use existing Bind[newName] if possible
            val belowBind = bind.input
            val bindNewName = belowBind.parents.find {
                it !== bind && it is SNodeBind &&
                it.bindings.let { it.size == 1 && it[bindingPosition]?.equals(newName) ?: false }
            } ?: if (bind2parentsOverlap.isEmpty()) {
                // safe to do a destructive rename
                bind.bindings[bindingPosition] = newName
                bind.refreshSchema()
                bind
            } else SNodeBind(belowBind, mapOf(bindingPosition to newName)).apply { this.visited = belowBind.visited }

            if (bind !== bindNewName) {
                bind2parentsNoOverlap.forEach { bind2parent ->
                    bind2parent.inputs[bind2parent.inputs.indexOf(bind)] = bindNewName
                    bindNewName.parents += bind2parent
                    bind.parents -= bind2parent
                }
                if (bind.parents.isEmpty()) // eliminate bind
                    belowBind.parents -= bind
            }

            bind2parentsNoOverlap.toSet().forEach {
                renameUpward(oldName, newName, it, bindNewName)
            }

            if (LOG.isTraceEnabled)
                LOG.trace("RewriteBindUnify: unify binding $bindingPosition: $oldName -> $newName on ${bind.id} above ${belowBind.id}")
            return true
        }
        return false
    }

    private fun renameUpward(oldName: Name, newName: Name, node: SNode, inputFrom: SNode) {
        if( newName in node.schema ) {
            val bindingPosition = inputFrom.schema.names.indexOf(newName)
            // stop renaming upward; we have a name conflict
            val unbindNew = SNodeUnbind(inputFrom, mapOf(bindingPosition to newName)).apply { this.visited = inputFrom.visited }
            val bindOld = SNodeBind(unbindNew, mapOf(bindingPosition to oldName)).apply { this.visited = inputFrom.visited }
            node.inputs.mapInPlace {
                if( it == inputFrom ) {
                    inputFrom.parents -= node
                    bindOld.parents += node
                    bindOld
                } else it
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
        }
        // for each input to node, if it has oldName in its schema, add a Bind[newName] -> Unbind[oldName] -> child
        node.inputs.toSet().forEach { nodeInput ->
            if (oldName in nodeInput.schema) {
                // Modify in place if possible. Otherwise let future rules handle this.
                if (nodeInput is SNodeBind && oldName in nodeInput.bindings.values && nodeInput.parents.size == 1) {
                    nodeInput.bindings.mapValuesInPlace { if (it == oldName) newName else it }
                    nodeInput.refreshSchema()
                } else {
                    nodeInput.parents.removeIf { it == node }
                    val bindingPosition = nodeInput.schema.names.indexOf(oldName)
                    val unbindOld = SNodeUnbind(nodeInput, mapOf(bindingPosition to oldName)).apply { this.visited = nodeInput.visited }
                    val bindNew = SNodeBind(unbindOld, mapOf(bindingPosition to newName)).apply { this.visited = nodeInput.visited }
                    node.inputs.mapInPlace {
                        if (it == nodeInput) {
                            bindNew.parents += node
                            bindNew
                        } else it
                    }
                }
            }
        }
        node.refreshSchema()
        // Recurse to renaming parents above
        node.parents.toSet().forEach { renameUpward(oldName, newName, it, node) }
    }


}

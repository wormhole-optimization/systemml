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

            // bind-unbind or unbind-bind with common bindings -- eliminate the common ones
            // Split CSE if foreign parent present on node.
            val above = node.parents.find { it.isBindOrUnbind() && it.javaClass != node.javaClass
                    && it.agBindings().any { (p,n) -> node.agBindings()[p] == n }
            }
            if( above != null ) {
                // above can only be a parent once because it is a bind/unbind
                val otherNodeParents = node.parents.filter { it !== above }
                if( otherNodeParents.isNotEmpty() ) {
                    // Split CSE: connect otherNodeParents to a copy of node
                    val copy = node.shallowCopyNoParentsYesInputs()
                    otherNodeParents.forEach {
                        it.inputs[it.inputs.indexOf(node)] = copy
                        copy.parents += it
                        node.parents -= it
                    }
                }
                // only parent of node is above :)
                assert(node.parents.size == 1)
                val commonBindings = node.agBindings().intersectEntries(above.agBindings())
                commonBindings.forEach { (k,_) ->
                    node.agBindings() -= k
                    above.agBindings() -= k
                }

                if( above.agBindings().isEmpty() )
                    RewriteBindElim.eliminateEmpty(above)
                val newNode = if( node.agBindings().isEmpty() ) RewriteBindElim.eliminateEmpty(node) else node
                if( LOG.isTraceEnabled )
                    LOG.trace("RewriteBindUnify: elim redundant bindings $commonBindings in ${node.id} $above -- ${node.id} $node ${if(otherNodeParents.isNotEmpty()) "(with split CSE)" else ""}")
                return rRewriteBindUnify(newNode, true)
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
                val commonBindingPositions = bind1.bindings.keys.intersect(bind2.bindings.keys).filter { bind1.bindings[it]!! != bind2.bindings[it]!! }
                if( commonBindingPositions.isNotEmpty() ) {
                    val bindingPosition = commonBindingPositions.first()
                    val newName = bind1.bindings[bindingPosition]!!
                    val oldName = bind2.bindings[bindingPosition]!!
                    val (bind2parentsOverlap, bind2parentsNoOverlap) = bind2.parents.partition { newName in it.schema || it.visited }
                    if( bind2parentsNoOverlap.isNotEmpty() ) {
                        // Create new bind on this position to the new name:
                        // bind2parentParents -> Bind[oldName] -> Unbind[newName] -> bind2parent -> Bind[newName] -> node

                        // Use existing Bind[newName] if possible
                        val bindNewName = bindIndices.find {
                            (node.parents[it] as SNodeBind).bindings.let { it.size == 1 && it[bindingPosition]?.equals(newName) ?: false }
                        }?.let { node.parents[it] }
                                ?: if( bind2parentsOverlap.isEmpty() ) {
                            // safe to do a destructive rename
                            bind2.bindings[bindingPosition] = newName
                            bind2.refreshSchema()
                            bind2
                        } else
                            SNodeBind(node, mapOf(bindingPosition to newName))

                        if( bind2 !== bindNewName ) {
                            bind2parentsNoOverlap.forEach { bind2parent ->
                                bind2parent.inputs[bind2parent.inputs.indexOf(bind2)] = bindNewName
                                bindNewName.parents += bind2parent
                                bind2.parents -= bind2parent
                            }
                            if( bind2.parents.isEmpty() ) // eliminate bind2
                                node.parents -= bind2
                        }
                        bind2parentsNoOverlap.forEach { bind2parent ->
                            // for each input to bind2parent, if it has oldName in its schema, add a Bind[newName] -> Unbind[oldName] -> child
                            bind2parent.inputs.toSet().forEach { bind2parentInput ->
                                if( oldName in bind2parentInput.schema ) {
                                    // Modify in place if possible. Otherwise let future rules handle this.
                                    if( bind2parentInput is SNodeBind && oldName in bind2parentInput.bindings.values && bind2parentInput.parents.size == 1 ) {
                                        bind2parentInput.bindings.mapValuesInPlace { if( it == oldName ) newName else it }
                                        bind2parentInput.refreshSchema()
                                    } else {
                                        bind2parentInput.parents.removeIf { it == bind2parent }
                                        val unbindOld = SNodeUnbind(bind2parentInput, mapOf(bindingPosition to oldName))
                                        val bindNew = SNodeBind(unbindOld, mapOf(bindingPosition to newName))
                                        bind2parent.inputs.mapInPlace {
                                            if (it == bind2parentInput) {
                                                bindNew.parents += bind2parent
                                                bindNew
                                            } else it
                                        }
                                    }
                                }
                            }
                            bind2parent.refreshSchema()
                        }

                        bind2parentsNoOverlap.toSet().forEach { bind2parent ->
                            val bind2parentParentSet = bind2parent.parents.toSet()
                            val (nonUnbind, unbind) = bind2parentParentSet.partition { it !is SNodeUnbind || oldName !in it.unbindings.values }
                            unbind.forEach { (it as SNodeUnbind).unbindings.mapValuesInPlace { if( it == oldName ) newName else it } }
                            if( nonUnbind.isNotEmpty() ) {
                                val unbindNew = SNodeUnbind(bind2parent, mapOf(bindingPosition to newName))
                                val bindOld = SNodeBind(unbindNew, mapOf(bindingPosition to oldName))
                                nonUnbind.forEach { bind2parentParent ->
                                    bind2parentParent.inputs.withIndex().filter { (_, input) -> input == bind2parent }.map { (i, _) -> i }.forEach {
                                        bind2parentParent.inputs[it] = bindOld
                                        bindOld.parents += bind2parentParent
                                        bind2parent.parents -= bind2parentParent
                                    }
                                }
                            }
                        }
                        if( LOG.isTraceEnabled )
                            LOG.trace("RewriteBindUnify: unify binding $bindingPosition: $oldName(${bind1.id}) -> $newName(${bind2.id}) above ${node.id}")
                        return rRewriteBindUnify(node, true)
                    }
                }
            }
        }


        return if (changed) RewriteResult.NewNode(node) else RewriteResult.NoChange
    }


}

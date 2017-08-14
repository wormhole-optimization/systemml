package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriteRule.RewriteResult

/**
 * Eliminate pairs of Bind-Unbind.
 *
 * Given the pattern
 * ```
 * +a  +b
 *  \ /
 *   A
 * ```
 * attempt to change the `b` to `a` for the operation above `b`.
 * Suppose `X` has `a` in its schema and `Y` does not.
 * Suppose `C` has `b` in its schema and `D` does not.
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
 *
 */
class RewriteBindUnify : SPlanRewriteRuleBottomUp() {

    override fun rewriteNodeUp(node: SNode): RewriteResult {
        return rRewriteBindUnify(node, false)
    }
    private tailrec fun rRewriteBindUnify(node: SNode, changed: Boolean): RewriteResult {
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

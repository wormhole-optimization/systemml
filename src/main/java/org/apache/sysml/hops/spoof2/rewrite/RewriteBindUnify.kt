package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.spoof2.enu.ENode
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriteRule.RewriteResult
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

    override fun rewriteNodeUp(node: SNode) = rRewriteBindUnify(node, false)
    private tailrec fun rRewriteBindUnify(node: SNode, changed: Boolean): RewriteResult {
        if( node.isBindOrUnbind() ) {
            // empty bind/unbind
            if( node.agBindings().isEmpty() ) {
                val child = RewriteBindElim.eliminateNode(node)
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
                RewriteBindElim.eliminateNode(killParent)
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
                above.refreshSchemasUpward() // insidious situation: The unbind in unbind-bind shifts the indices

                if (above.agBindings().isEmpty())
                    RewriteBindElim.eliminateNode(above)
                val newNode = if (node.agBindings().isEmpty()) RewriteBindElim.eliminateNode(node) else node
                if (LOG.isTraceEnabled)
                    LOG.trace("RewriteBindUnify: elim redundant bindings $commonBindings in ${above.id} $above -- ${node.id} $node ${if (otherNodeParents.isNotEmpty()) "(with split CSE)" else ""} to yield ${newNode.id} $newNode")
                return rRewriteBindUnify(newNode, true)
            }

            // unbind-bind-unbind or bind-unbind-bind with disjoint mappings on the common one
            // e.g. unbind[0]-bind[0]-unbind[1] --> unbind[0,1]-bind[0]
            // e.g. bind[0]-unbind[0]-bind[1] --> bind[0,1]-unbind[0]
            val a2 = node.parents.find { it.isBindOrUnbind() && it.javaClass != node.javaClass }
            if( a2 != null ) {
                val a3 = a2.parents.find {
                    it.javaClass == node.javaClass
                            && it.agBindings().keys.disjoint(a2.agBindings().keys)
                            && it.agBindings().keys.disjoint(node.agBindings().keys)
                            && it.agBindings().values.disjoint(a2.agBindings().values)
                }
                if (a3 != null) {
                    if( node.parents.size > 1 || a2.parents.size > 1 ) {
                        if( LOG.isInfoEnabled )
                            LOG.info("Skipping opportunity to combine $node <- $a2 <- $a3 due to foreign parents; todo add this functionality")
                    } else {
                        if (LOG.isTraceEnabled)
                            LOG.trace("RewriteBindUnify: combine disjoint triple (${node.id}) $node <- $a2 <- $a3, eliminating (${a3.id}) $a3")
                        node.agBindings().putAll(a3.agBindings())
                        a3.agBindings().clear()
                        RewriteBindElim.eliminateNode(a3)
                        node.refreshSchema()
                        a2.refreshSchema()
                        return rRewriteBindUnify(node, true)
                    }
                }
            }
        }

        if( node is SNodeUnbind ) {
            // unbind-bind with different bindings - try to unify
            val above = node.parents.find { it is SNodeBind && !it.bindings.keys.disjoint(node.unbindings.keys)
                    && it.parents.none { it is SNodeBind } } // if there is another bind above this bind, do not proceed; first advance to the bind and combine consecutive binds.
            if( above != null ) {
                above as SNodeBind
                for (unbindBindPos in node.unbindings.keys
                        .intersect(above.bindings.keys)
                        .filter { node.unbindings[it]!! != above.bindings[it]!! }) {
                    // if aboveName < nodeName, then rename aboveName to nodeName and propagate up
                    // if nodeName < aboveName, then rename nodeName to aboveName and propagate down
                    val aboveName = above.bindings[unbindBindPos]!!
                    val nodeName = node.unbindings[unbindBindPos]!!
                    // exception: if aboveName has a parent that is an SNodeAggregate, then reverse the ordering
                    val flip = above.parents.any { it is SNodeAggregate && nodeName in it.aggs }
                    val success = if(aboveName > nodeName) // flip!
                        tryRenameSingle(above, aboveName, nodeName)
                    else
                        tryRenameSingle(node, nodeName, aboveName)
                    if( success )
                        return rRewriteBindUnify(node, true)
                }
            }
        }

        // bind-unbind-bind with changing positions - try to collapse transpose
        // only applies when the bottom bind (node) has foreign parents; otherwise other rules handle this case
        if( node is SNodeBind  ) { // node.parents.size > 1
            // p1Unbind may have fewer bindings
            val p1Unbind = node.parents.find { it is SNodeUnbind && node.bindings.values.containsAll(it.unbindings.values) } as? SNodeUnbind
            if( p1Unbind != null ) {
                // p2Bind binds to the same positions as p1Unbind
                val p2Bind = p1Unbind.parents.find { it is SNodeBind && it.bindings.keys == p1Unbind.unbindings.keys } as? SNodeBind
                if( p2Bind != null ) {
                    val newBindings = node.bindings.mapValues { (_,n) ->
                         if( n in p1Unbind.unbindings.inverse() ) p2Bind.bindings[p1Unbind.unbindings.inverse()[n]]!!
                         else n
                    }

                    // Split the bottom bind (node) and wire it to the parents of p2Bind
                    val belowBind = node.input
                    // reuse an existing bind if possible
                    val bindNewName = belowBind.parents.find {
                        it !== node && it is SNodeBind &&
                                it.bindings == newBindings
                    } ?: if (node.parents.size == 1 && p1Unbind.parents.size == 1) {
                        // safe to do a destructive rename
                        node.bindings.clear()
                        node.bindings.putAll(newBindings)
                        node.refreshSchema()
                        node
                    } else SNodeBind(belowBind, newBindings).apply { this.visited = belowBind.visited }

                    p1Unbind.parents -= p2Bind
                    if( p1Unbind.parents.isEmpty() )
                        node.parents -= p1Unbind
                    p2Bind.parents.forEach {
                        it.inputs[it.inputs.indexOf(p2Bind)] = bindNewName
                        bindNewName.parents += it
                    }
                    val nn = if( node.parents.isEmpty() ) {
                        belowBind.parents -= node
                        node.input
                    } else node
                    bindNewName.parents.forEach { it.refreshSchemasUpward() }

                    if (LOG.isTraceEnabled)
                        LOG.trace("RewriteBindUnify: eliminate transpose-like renaming pattern (${p2Bind.id}) $p2Bind -- (${p1Unbind.id}) $p1Unbind -- (${node.id}) $node")
                    return rRewriteBindUnify(nn, true)
                }
            }
        }

        // check if two parents have a Bind to the same dimension. If so, try to unify them.
        val bindIndices = node.parents.withIndex().filter { (_,p) -> p is SNodeBind }.map { (i,_) -> i }
        for( bindi in 0..bindIndices.size-2) {
            val bind1 = node.parents[bindIndices[bindi]] as SNodeBind
            for( bindj in bindi+1 until bindIndices.size) {
                // see if there is overlap. If so, try renaming the bindj to bindi
                val bind2 = node.parents[bindIndices[bindj]] as SNodeBind
                // Common positions that map to different names
                for( bindingPosition in bind1.bindings.keys
                        .intersect(bind2.bindings.keys)
                        .filter { bind1.bindings[it]!! != bind2.bindings[it]!! }) {
                    val name1 = bind1.bindings[bindingPosition]!!
                    val name2 = bind2.bindings[bindingPosition]!!
                    val success = if( name1 > name2 ) // flip!
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

    companion object {
        fun SNode.isBindOrUnbind() = this is SNodeBind || this is SNodeUnbind

//        fun renameTwoSteps(node: SNode, desiredBindings: Map<AU, AB>): Boolean {
//            if( !node.isBindOrUnbind() )
//                return false
//            val desiredNames = desiredBindings.filter { (p, desiredName) ->
//                node.agBindings().let {
//                    if( p !in it )
//                        throw SNodeException(node, "does not have a binding for $p; desired $desiredBindings")
//                    it[p] != desiredName
//                }
//            }
//            val oldNames = node.agBindings().filter { (p, _) -> p in desiredNames }
//            val intermediateNames = oldNames.mapValues { (_, oldName) -> oldName.deriveFresh() }
//            val oldToIntermediate = oldNames.map { (p, oldName) -> oldName to intermediateNames[p]!! }.toMap()
//            val intermediateToNew = intermediateNames.map { (p, intermediateName) -> intermediateName to desiredNames[p]!! }.toMap()
//            val success1 = forceRenameAll(node, oldToIntermediate)
//            if( !success1 )
//                throw SNodeException(node, "problem renaming to intermediate via $oldToIntermediate")
//            val success2 = forceRenameAll(node, intermediateToNew)
//            if( !success2 )
//                throw SNodeException(node, "problem renaming to new via $intermediateToNew")
//            return true
//        }
//
//        fun forceRenameAll(node: SNode, oldToNew: Map<AB,AB>): Boolean {
//            if( !node.isBindOrUnbind() )
//                return false
//            for ((oldName, newName) in oldToNew) {
//                val success = tryRenameSingle(node, oldName, newName)
//                if( !success )
//                    throw SNodeException(node, "failed to rename $oldName to $newName on this node during forceful rename all $oldToNew")
//            }
//            return true
//        }

        private fun BAD_COND(newName: AB, it: SNode): Boolean =
            newName in it.schema || (it is SNodeAggregate && newName in it.aggs) || it is ENode || it is SNodeUnbind && newName in it.unbindings.values

        private fun BAD_COND_REC(newName: AB, it: SNode): Boolean =
            if( it.isBindOrUnbind() ) it.parents.all { BAD_COND_REC(newName, it) }
            else BAD_COND(newName, it)


        /**
         * Try to rename [oldName] to [newName] in [node]. If successful, propagate the renaming.
         *
         * If [node] is [SNodeBind], it is successful if at least one parent of [node] does not have [newName] in its schema,
         * and the propagation is upward.
         * If [node] is [SNodeUnbind], it is successful if [node]'s input does not have [newName] in its schema,
         * and the propagation is downward.
         */
        fun tryRenameSingle(node: SNode, oldName: AB, newName: AB): Boolean {
            if( !node.isBindOrUnbind() || oldName == newName || newName in node.schema || oldName !in node.agBindings().values )
                return false

            if (node is SNodeUnbind) {
                if (newName in node.unbindings.values )
                    return false
                if (!BAD_COND_REC(newName, node.input)) {
                    val bindingPosition = node.unbindings.entries.find { (_, n) -> n == oldName }!!.key
                    node.unbindings.mapValuesInPlace { if (it == oldName) newName else it }
                    rRenamePropagate(oldName, newName, node.input, node)
                    if (LOG.isTraceEnabled)
                        LOG.trace("RewriteBindUnify: downward propagate rename $bindingPosition: $oldName -> $newName on ${node.id}")
                    return true
                }
            } else {
                node as SNodeBind
                // filter parents based on whether they are eligible for at least one step of renaming. Avoid bind-unbind traps.
                val (bind2parentsOverlap, bind2parentsNoOverlap) = node.parents.partition {
                    BAD_COND_REC(newName, it)
                }
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
                        if (newName !in it.schema
                                &&  (it !is SNodeAggregate || newName !in it.aggs) && it !is ENode && (it !is SNodeUnbind || newName !in it.unbindings.values)
                                ) // we may handle a parent in the middle of rRenamePropagate
                            rRenamePropagate(oldName, newName, it, bindNewName)
                    }

                    if (LOG.isTraceEnabled)
                        LOG.trace("RewriteBindUnify: upward propagate rename $bindingPosition: $oldName -> $newName on ${node.id} above ${belowBind.id}, starting with ${bindNewName.id}")
                    return true
                }
            }
            return false
        }

        private fun rRenamePropagate(oldName: AB, newName: AB, node: SNode, fromNode: SNode) {
            val refreshParentsList = LinkedList<SNode>()
            rRenamePropagate(oldName, newName, node, fromNode, refreshParentsList)
            refreshParentsList.forEach { n ->
                n.parents.toSet().forEach {
                    if (oldName in it.schema || (it is SNodeUnbind && oldName in it.unbindings.values) || it is SNodeAggregate && oldName in it.aggs)
                        rRenamePropagate(oldName, newName, it, n)
                }
            }
        }

        /**
         * Propagate the name change from [oldName] to [newName] throughout the DAG.
         * The initial call to this method is on the first [node] on which the renaming is to occur
         * and is initiated from [fromNode], which is either a parent or child of [node].
         *
         * Stop Condition 1:
         * If [newName] is in [node]'s schema
         *  or [newName] is in an Agg's aggregateNames
         *  or [newName] is in an Unbind's bindings
         *  or we reach an [ENode],
         * then we cannot do the rename here; either
         * (a) if [fromNode] is a child of [node], then replace the input leading to [fromNode] as
         *     `node -> Bind[oldName] -> Unbind[newName] -> fromNode`, or
         * (b) if [fromNode] is a parent of [node], then replace the parent leading to [fromNode] as
         *     `fromNode -> Bind[newName] -> Unbind[oldName] -> node`.
         *
         * Stop Condition 2:
         * * If we reach an [SNodeAggregate] whose aggregate names include [oldName], then change it to [newName] and stop.
         *   (We must have entered the agg from below, because [oldName] is not in scope above the agg.)
         * * If we reach an [SNodeUnbind] that unbinds [oldName], then change it to unbinding [newName] and stop.
         *   (We must have entered the unbind from below, because [oldName] is not in scope above the agg.)
         * * If we reach an [SNodeBind] that binds [oldName], then change it to binding [newName] and stop.
         *   (We must have entered the bind from above, because [oldName] is not in scope below the bind.)
         *   **But continue with bind's other parents after the recursion!**
         *
         * If we do not meet a stopping condition, then continue the propagation.
         * Include inputs that have [oldName] in its schema.
         * Include all parents
         * Exclude [fromNode].
         *
         * @param refreshParentsList A list of nodes whose parents should be checked for propagation after the recursion finishes
         */
        private fun rRenamePropagate(oldName: AB, newName: AB, node: SNode, fromNode: SNode, refreshParentsList: MutableList<SNode>) {
            val fromInput = fromNode in node.inputs
            if (LOG.isTraceEnabled)
                LOG.trace("at (${node.id}) $node ${node.schema} from ${if (fromInput) "input" else "parent"} (${fromNode.id}) $fromNode")
            // Stop on Name Conflict.
//        if( node is SNodeAggregate && newName in node.aggs )
//            return
            if (newName in node.schema || node is SNodeAggregate && newName in node.aggs || node is ENode || node is SNodeUnbind && newName in node.unbindings.values) {
                if (fromInput) {
                    val au = fromNode.schema.leastFreeUnbound() //fromNode.schema.names.indexOf(newName)
                    val unbindNew = SNodeUnbind(fromNode, mapOf(au to newName)).apply { this.visited = fromNode.visited }
                    val bindOld = SNodeBind(unbindNew, mapOf(au to oldName)).apply { this.visited = fromNode.visited }
                    node.inputs.mapInPlace {
                        if (it == fromNode) {
                            fromNode.parents -= node
                            bindOld.parents += node
                            bindOld
                        } else it
                    }
                } else {
                    val au = node.schema.leastFreeUnbound()
                    val unbindOld = SNodeUnbind(node, mapOf(au to oldName)).apply { this.visited = node.visited }
                    val bindNew = SNodeBind(unbindOld, mapOf(au to newName)).apply { this.visited = node.visited }
                    fromNode.inputs.mapInPlace {
                        if (it == node) {
                            node.parents -= fromNode
                            bindNew.parents += fromNode
                            bindNew
                        } else it
                    }
                }
                return
            }
            // Stop when closing the scope of oldName via Agg or Unbind. (These have a single input.)
            when (node) {
                is SNodeAggregate -> {
                    if (oldName in node.aggs) {
                        node.aggs.replaceKey(oldName, newName)
                        return
                    }
                }
                is SNodeUnbind -> {
                    if (oldName in node.unbindings.values) {
                        node.unbindings.mapValuesInPlace { if (it == oldName) newName else it }
                        return
                    }
                }
                is SNodeBind -> {
                    if (oldName in node.bindings.values) {
                        node.bindings.mapValuesInPlace { if (it == oldName) newName else it }
                        node.refreshSchema()
                        // refresh the parents of SNodeBind after the recursion finishes
                        if (node.parents.size > 1)
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
                // don't step into parents that we already visited (which can occur due to a loop: visiting a parent through an input)
                if (it != fromNode && (oldName in it.schema || it is SNodeAggregate && oldName in it.aggs || it is SNodeUnbind && oldName in it.unbindings.values) )
                    rRenamePropagate(oldName, newName, it, node, refreshParentsList)
            }
        }
    }

}

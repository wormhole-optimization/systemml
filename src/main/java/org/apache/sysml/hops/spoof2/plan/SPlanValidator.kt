package org.apache.sysml.hops.spoof2.plan


import java.util.ArrayList
import java.util.HashSet

import org.apache.commons.logging.LogFactory
import org.apache.sysml.runtime.DMLRuntimeException
import org.apache.sysml.utils.Explain


/**
 * This class allows to check node dags for validity, e.g., parent-child linking.
 * Use it for debugging (enabled in [org.apache.sysml.hops.rewrite.ProgramRewriter]).
 */
object SPlanValidator {
    private val LOG = LogFactory.getLog(SPlanValidator::class.java.name)

    fun validateSPlan(roots: ArrayList<SNode>?) {
        if (roots == null)
            return
        try {
            SNode.resetVisited(roots)
            val state = ValidatorState()
            for (node in roots)
                rValidateNode(node, state)
            SNode.resetVisited(roots)
            checkAllRootsAreReal(roots, state)
        } catch (ex: SNodeException) {
            try {
                LOG.error("\n" + Explain.explainSPlan(roots, true), ex)
            } catch (e: DMLRuntimeException) {}
            throw ex
        }

    }

    fun validateSPlan(root: SNode?) {
        if (root == null)
            return
        try {
            root.resetVisited()
            val state = ValidatorState()
            rValidateNode(root, state)
            root.resetVisited()
            checkAllRootsAreReal(listOf(root), state)
        } catch (ex: SNodeException) {
            try {
                LOG.error("\n" + Explain.explain(root, true), ex)
            } catch (e: DMLRuntimeException) {}
            throw ex
        }

    }

    private fun checkAllRootsAreReal(roots: List<SNode>, state: ValidatorState) {
        state.seen.clear()
        state.leaves.forEach { rCheckAllRootsAreReal(roots, state, it) }
    }

    private fun rCheckAllRootsAreReal(roots: List<SNode>, state: ValidatorState, node: SNode) {
        if( node.id in state.seen )
            return
        state.seen += node.id
        if( node.parents.isEmpty() )
            node.check(node in roots) {"A no-parent node is reachable from the leaves but is not a root. Children: ${node.inputs}"}
        else {
            node.parents.forEach { rCheckAllRootsAreReal(roots, state, it) }
        }
    }

    private class ValidatorState {
        internal val seen: MutableSet<Long> = HashSet()
        internal val leaves: MutableSet<SNode> = HashSet()
    }

    @Throws(SNodeException::class)
    private fun rValidateNode(node: SNode, state: ValidatorState) {
        val id = node.id

        //check visit status
        val seen = !state.seen.add(id)
        if (seen != node.visited) {
            val parentIDs = node.parents.map(SNode::id)
            Explain.SHOW_VISIT_STATUS = true
            throw SNodeException(node, "problem with visit status, incorrectly set to ${node.visited}; parentIDs=$parentIDs")
        }
        if (seen) return  // we saw the Node previously, no need to re-validate

        //check parent linking
        for (parent in node.parents)
            node.check(node in parent.inputs) {"not properly linked to its parent pid=${parent.id} $parent"}

        val inputs = node.inputs

        //check child linking
        for (child in inputs)
            node.check(node in child.parents) {"not properly linked to its child cid=${child.id} $child"}

        //check empty children (other variable-length Nodes must have at least one child)
        if (inputs.isEmpty()) {
            node.check(node is SNodeData || node is SNodeExt)
            {"is not a data or ext SNode but has no children"}
            state.leaves += node
        }

        // check Node has a legal arity (number of children)
        node.checkArity()

        // maybe check bind/unbind properties

        //recursively process children
        for (child in inputs)
            rValidateNode(child, state)

        // check if schema is up to date
        val oldSchema = Schema(node.schema)
        node.refreshSchema()
        // Check names, not shapes; shapes may be messed up due to Structural CSE Elim
        node.check( node.schema.names == oldSchema.names ) {"refreshing changed schema from old schema $oldSchema"}
        node.check( node.schema.names.filter(Name::isBound).let { it.toSet().size == it.size }) {"duplicate bound names: ${node.schema}"}


        node.visited = true
    }
}

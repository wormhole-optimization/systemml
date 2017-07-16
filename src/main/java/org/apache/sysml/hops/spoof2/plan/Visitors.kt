package org.apache.sysml.hops.spoof2.plan

import org.apache.sysml.hops.spoof2.plan.SNode.Companion.FN_RET

/** Rename attribute names throughout this sub-DAG.
 * Assumes the new names do not conflict with existing names. */
fun SNode.renameAttributes(renaming: Map<Name, Name>, useInternalGuard: Boolean) {
    val postVisit: (SNode, Boolean) -> Boolean = { it, c ->
        var changed = c
        when( it ) {
            is SNodeAggregate -> {
                changed = it.aggreateNames.mapInPlace { renaming[it] ?: it } || changed
            }
            is SNodeUnbind -> {
                changed = it.unbindings.mapValuesInPlace { renaming[it] ?: it } || changed
            }
            is SNodeBind -> {
                changed = it.bindings.mapValuesInPlace { renaming[it] ?: it } || changed
            }
        }
        if (changed)
            it.refreshSchema()
        changed
    }
    val oldSchema = Schema(this.schema)
    acceptFoldUnorderedGuard(SNode.FN_NULL, postVisit, false, Boolean::or)
    // if the schema changed as a result of the rename, then the parents may need to change too
    // specifically: the schema may be reordered
    if( this.schema != oldSchema )
        this.parents.forEach { it.refreshSchemasUpward() }
}

/**
 * Refresh the schema. If it changed, refresh the schema of all parents recursively.
 *
 * @return Whether the schema of this node changed.
 */
fun SNode.refreshSchemasUpward(): Boolean {
    val origSchema = Schema(this.schema)
    this.refreshSchema()
    if( origSchema != this.schema ) // only if schema changed (also acts as a memo guard)
    {
        this.parents.forEach { it.refreshSchemasUpward() }
        return true
    } else return false
}

/**
 * Is this SNode and all children recursively composed of entirely SNodeDatas and SNodeExts
 * and `==` SNodeNarys?
 */
fun SNode.isEntirelyDataExtEquals(): Boolean {
    val preVisit: (SNode) -> Boolean? = { node ->
        if (node !is SNodeData && node !is SNodeExt
                && (node !is SNodeNary || node.op != SNodeNary.NaryOp.EQUAL))
            false // no need to visit children; we know the result is false
        else null
    }
    val postVisit: (SNode, Boolean) -> Boolean = ::FN_RET // directly return the Boolean
    return acceptFoldUnordered(preVisit, postVisit, true, Boolean::and) // no memo guard because this is really cheap
}


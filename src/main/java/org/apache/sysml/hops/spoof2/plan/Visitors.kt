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
    acceptFoldUnorderedGuard(SNode.FN_NULL, postVisit, false, Boolean::or)
}

fun SNode.refreshSchemasUpward() {
    val origSchema = Schema(this.schema)
    this.refreshSchema()
    if( origSchema != this.schema ) // only if schema changed (also acts as a memo guard)
        this.parents.forEach { it.refreshSchemasUpward() }
}

/**
 * Is this SNode and all children recursively composed of entirely SNodeDatas and SNodeExts?
 */
fun SNode.isEntirelyDataExt(): Boolean {
    val preVisit: (SNode) -> Boolean? = { node ->
        if (node !is SNodeData && node !is SNodeExt)
            false // no need to visit children if this is not Data or Ext; we know the result is false
        else null
    }
    val postVisit: (SNode, Boolean) -> Boolean = ::FN_RET // directly return the Boolean
    return acceptFoldUnordered(preVisit, postVisit, true, Boolean::and) // no memo guard because this is really cheap
}


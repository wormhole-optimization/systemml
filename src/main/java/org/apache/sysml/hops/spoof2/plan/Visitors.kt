package org.apache.sysml.hops.spoof2.plan

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
                changed = it.unbinding.mapInPlace { renaming[it] ?: it } || changed
            }
            is SNodeBind -> {
                changed = it.bindings.mapValuesInPlace { renaming[it] ?: it } || changed
            }
            is SNodePermute -> {
                changed = it.permutation.mapInPlace { k,v -> (renaming[k] ?: k) to (renaming[v] ?: v) } || changed
            }
        }
        if (changed)
            it.refreshSchema()
        changed
    }
    acceptFoldUnorderedGuard(SNode.FN_NULL, postVisit, false, Boolean::or)
}

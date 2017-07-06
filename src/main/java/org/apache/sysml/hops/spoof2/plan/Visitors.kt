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


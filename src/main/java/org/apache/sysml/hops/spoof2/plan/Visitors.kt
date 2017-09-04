package org.apache.sysml.hops.spoof2.plan

import org.apache.sysml.hops.recompile.Recompiler
import org.apache.sysml.hops.spoof2.plan.SNode.Companion.FN_RET

/** Rename attribute names throughout this sub-DAG.
 * Assumes the new names do not conflict with existing names. */
fun SNode.renameAttributes(renaming: Map<Name, Name>, useInternalGuard: Boolean) {
    val postVisit: (SNode, Boolean) -> Boolean = { it, c ->
        var changed = c
        when( it ) {
            is SNodeAggregate -> {
                changed = it.aggs.names.mapInPlace { renaming[it] ?: it } || changed
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


fun SNode.refreshSchemasUpwardPermuteName(): Boolean {
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

fun SNodeAggregate.copyAggRenameDown(): SNodeAggregate {
    val renaming = this.aggs.names.map { it to Schema.freshNameCopy(it) }.toMap()
    val aggInput = this.inputs[0].renameCopyDown(renaming, HashMap())
    val agg = SNodeAggregate(this.op, aggInput, Schema.copyShapes(aggInput.schema, renaming.values))
    return agg
}


private fun SNode.renameCopyDown(renaming: Map<Name, Name>, memo: HashMap<Long, SNode>): SNode {
    check( this.schema.names.containsAll(renaming.keys) ) {"renameCopyDown should only touch SNodes that have a schema to rename; saw id=${this.id} $this ${this.schema}"}
    if( this.id in memo )
        return memo[this.id]!!
    val newNode = when( this ) {
        is SNodeBind -> {
            val b = this.bindings.mapValues { (_,n) -> renaming[n] ?: n }
            val r = renaming.filter { (orig,_) -> orig !in this.bindings.values }
            val i: SNode = if( r.isNotEmpty() ) this.inputs[0].renameCopyDown(r, memo) else this.inputs[0]
            SNodeBind(i, b)
        }
        is SNodeAggregate -> SNodeAggregate(this.op, this.inputs[0].renameCopyDown(renaming, memo), this.aggs)
        is SNodeNary -> {
            SNodeNary(this.op, this.inputs.map { input ->
                val renamingIntersect = renaming.filterKeys { it in input.schema.names }
                if( renamingIntersect.isNotEmpty() )
                    input.renameCopyDown(renamingIntersect, memo)
                else input
            })
        }
        is SNodeUnbind -> SNodeUnbind(this.inputs[0].renameCopyDown(renaming, memo), this.unbindings)
        is SNodeData -> throw AssertionError("should not reach an SNodeData; should hit a Bind first") // Write Hops cannot have parents, right?
        is SNodeExt -> SNodeExt(Recompiler.deepCopyHopsDag(this.hop), this.inputs.map { it.renameCopyDown(renaming, memo) })
        else -> throw AssertionError("unknown SNode $this")
    }
    memo[this.id] = newNode
    return newNode
}

/**
 * Count the nodes in this SPlan for which [pred] evaluates to true.
 */
fun countPred(roots: ArrayList<SNode>, pred: (SNode) -> Boolean): Int {
    SNode.resetVisited(roots)
    val cnt = roots.sumBy { rCountPred(it, pred) }
    SNode.resetVisited(roots)
    return cnt
}
private fun rCountPred(node: SNode, pred: (SNode) -> Boolean): Int {
    if( node.visited ) // already counted
        return 0
    node.visited = true
    val cnt = if( pred(node) ) 1 else 0
    return cnt + node.inputs.sumBy { rCountPred(it, pred) }
}



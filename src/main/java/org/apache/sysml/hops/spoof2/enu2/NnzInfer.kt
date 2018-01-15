package org.apache.sysml.hops.spoof2.enu2

import org.apache.sysml.hops.spoof2.plan.*

object NnzInfer {

    fun inferNnz(roots: List<SNode>, memo: MutableMap<Id, Nnz>) {
        roots.forEach { inferNnz(it, memo) }
    }

    fun inferNnz(node: SNode, memo: MutableMap<Id, Nnz>): Nnz {
        if (node.id in memo)
            return memo[node.id]!!
        val (nextNodes, nodeNnz) = when( node ) {
            is SNodeData -> {
                val nnz = if (node.isLiteral)
                    if (node.isLiteralNumeric && node.literalDouble == 0.0) 0L else 1L
                else node.hop.nnz
                node.inputs to nnz
            }
            is SNodeExt -> node.inputs to node.hop.nnz
            is SNodeNary -> inferNnzNary(node, memo)
            is SNodeAggregate -> inferNnzAgg(node, memo)
            is OrNode -> listOf<SNode>() to inferNnz(node.inputs.first(), memo) // maybe need to take min of all children, because some may have more accurate estimates than others
            else -> throw AssertionError("unexpected: $node")
        }
        memo[node.id] = nodeNnz
        nextNodes.forEach { inferNnz(it, memo) }
        return nodeNnz
    }

    /**
     * Worst case estimates, assumes nz divided evenly among output cells:
     * If input is *: Π_{*-inputs} min(1, nnz/Π_{shapes-in-output}).
     * If input is not *: min(1, nnz/Π_{shapes-in-output}).
     */
    private fun inferNnzAgg(node: SNodeAggregate, memo: MutableMap<Id, Nnz>): Pair<List<SNode>, Nnz> {
        val below = if (node.input is SNodeNary && (node.input as SNodeNary).op == SNodeNary.NaryOp.MULT)
            node.input.inputs
        else listOf(node.input)
        val sp = below.map {
            minOf(1.0, inferNnz(it, memo).toDouble() /
                    it.schema.filter { n, _ -> n in node.schema }.shapes.prod())
        }.prod()
        val nnz = (sp * node.schema.shapes.prod()).toLong()
        return node.inputs to nnz
//        return node.inputs to node.schema.shapes.prod()
    }

    /**
     * Worst case estimates, assumes nz overlap completely.
     * *: min of sparsities.
     * +: min(1, sum of sparsities).
     */
    private fun inferNnzNary(node: SNodeNary, memo: MutableMap<Id, Nnz>): Pair<List<SNode>,Nnz> {
        val inputSparsities = node.inputs.map { inferNnz(it, memo).toDouble() / it.schema.shapes.prod() }
        val sp = when (node.op) {
            SNodeNary.NaryOp.MULT, SNodeNary.NaryOp.AND -> inputSparsities.min()!!
            SNodeNary.NaryOp.PLUS, SNodeNary.NaryOp.MINUS,
            SNodeNary.NaryOp.LESS, SNodeNary.NaryOp.GREATER, SNodeNary.NaryOp.NOTEQUAL,
            SNodeNary.NaryOp.MIN, SNodeNary.NaryOp.MAX,
            SNodeNary.NaryOp.OR -> minOf(1.0, inputSparsities.sum())
            SNodeNary.NaryOp.DIV, SNodeNary.NaryOp.MODULUS, SNodeNary.NaryOp.POW -> inputSparsities.first()
            else -> 1.0
        }
        val nnz = (sp*node.schema.shapes.prod()).toLong()
        return node.inputs to nnz
//        return node.inputs to node.schema.shapes.prod()
    }

}
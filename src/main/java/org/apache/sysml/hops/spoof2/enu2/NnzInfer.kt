package org.apache.sysml.hops.spoof2.enu2

import org.apache.sysml.hops.spoof2.plan.*

class NnzInfer(
        val inferer: NnzInferer
) {
    val memo: MutableMap<Id, Nnz> = mutableMapOf()

    fun infer(roots: List<SNode>) {
        roots.forEach { infer(it) }
    }

    fun infer(node: SNode): Nnz {
        // OrNode: maybe need to take min of all children, because some may have more accurate estimates than others
        if (node is SNodeBind || node is SNodeUnbind || node is OrNode)
            return infer(node.inputs[0])
        if (node.id in memo)
            return memo[node.id]!!
        val nodeNnz: Nnz = when( node ) {
            is SNodeData -> {
                if (node.isLiteral)
                    if (node.isLiteralNumeric && node.literalDouble == 0.0) 0L else 1L
                else node.hop.nnz
            }
            is SNodeExt -> node.hop.nnz
            is SNodeNary -> inferNnzNary(node)
            is SNodeAggregate -> inferNnzAgg(node)
            else -> throw AssertionError("unexpected: $node")
        }
        memo[node.id] = nodeNnz
        node.inputs.forEach { infer(it) }
        return nodeNnz
    }

    private fun inferNnzAgg(node: SNodeAggregate): Nnz {
        val d = node.schema
        if (node.input is SNodeNary && (node.input as SNodeNary).op == SNodeNary.NaryOp.MULT) {
            val (cz, cd) = node.input.inputs.map { infer(it) to it.schema }.unzip()
            return inferer.inferMatrixMult(d, cz, cd)
        }
        val cz = infer(node.input)
        val cd = node.input.schema
        return inferer.inferAgg(d, cz, cd)
    }

    private fun inferNnzNary(node: SNodeNary): Nnz {
        val d = node.schema
        val (cz, cd) = node.inputs.map { infer(it) to it.schema }.unzip()
        return when (node.op) {
            SNodeNary.NaryOp.MULT, SNodeNary.NaryOp.AND -> inferer.inferMult(d, cz, cd)
            SNodeNary.NaryOp.PLUS, SNodeNary.NaryOp.MINUS,
            SNodeNary.NaryOp.LESS, SNodeNary.NaryOp.GREATER, SNodeNary.NaryOp.NOTEQUAL,
            SNodeNary.NaryOp.MIN, SNodeNary.NaryOp.MAX,
            SNodeNary.NaryOp.OR -> inferer.inferAdd(d, cz, cd)
            SNodeNary.NaryOp.DIV, SNodeNary.NaryOp.MODULUS, SNodeNary.NaryOp.POW -> cz[0]
            else -> d.values.prod()
        }
    }

    fun infer(graph: Graph): Nnz {
        // collapse each edge group via Mult
        // across group nnz infer
        TODO()
    }
}
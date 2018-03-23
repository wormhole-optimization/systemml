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
                when {
                    node.isLiteral -> if (node.isLiteralNumeric && node.literalDouble == 0.0) 0L else 1L
                    node.hop.nnz >= 0 -> node.hop.nnz
                    else -> node.schema.shapes.prod() // use dense if unknown
                }
            }
            is SNodeExt -> when {
                node.hop.nnz >= 0 -> node.hop.nnz
                else -> node.schema.shapes.prod() // use dense if unknown
            }
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

    fun infer(bag: GraphBag): Nnz {
        val (cz, cd) = bag.map { g ->
            infer(g) to g.outs.map { it.a as Name to it.s }.toMap()
        }.unzip()
        val d = cd.reduce { a, b -> a+b }
        return inferer.inferAdd(d, cz, cd)
    }

    fun infer(graph: Graph, onlyBeforeAgg: Boolean = false): Nnz {
        if (graph.edges.isEmpty())
            return 1L
        // crude estimate: a graph is a Σ-*. Just do those
        val (cz, cd) = graph.edges.map { e ->
            infer(e) to e.verts.map { it.a as Name to it.s }.toMap()
        }.unzip()
        val md = cd.reduce { a, b -> a+b }
        val mz = inferer.inferMult(md, cz, cd)
        if (onlyBeforeAgg)
            return mz
        val d = graph.outs.map { it.a as Name to it.s }.toMap()
        return inferer.inferAgg(d, mz, md)
    }

    fun infer(e: Edge): Nnz = when (e) {
        is Edge.C -> infer(e.base)
        is Edge.F -> infer(e.base)
    }

}
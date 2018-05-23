package org.apache.sysml.hops.spoof2.enu2

import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.spoof2.plan.*

class PlanCost(
        val nnzInfer: NnzInfer
) {
//    override fun compareTo(other: SCost): Int = flops.compareTo(other.flops)
//    operator fun plus(c: SCost) = if( c == SCost.ZERO_COST ) this else SCost(this.flops + c.flops)
    val costMemo: MutableMap<Id, Double> = mutableMapOf()
    val nnzMemo: MutableMap<Id, Nnz> = nnzInfer.memo
    val recCostMemo: MutableMap<Id, Double> = mutableMapOf()
    val recChildrenMemo: MutableMap<Id, Set<SNode>> = mutableMapOf()

    // Removed in favor of calculating the cost non-recursively, due to sharing.
//    fun costSPlan(roots: List<SNode>,
//                  costMemo: MutableMap<Id, Double>, nnzMemo: MutableMap<Id, Nnz>): List<Double> {
//        if (COST_SPARSITY) {
//            WorstCaseNnz.infer(roots, nnzMemo)
//        }
//        return roots.map { costSPlan(it) }
//    }
//
//    private fun costSPlan(node: SNode,
//                          costMemo: MutableMap<Id, Double>, nnzMemo: MutableMap<Id, Nnz>): Double {
//        if( node.id in costMemo )
//            return costMemo[node.id]!!
//        var (nextNodes, nodeCost) = when( node ) {
//            is SNodeAggregate -> costAgg(node)
//            is SNodeNary -> costNary(node)
//            else -> node.inputs to 0.0
//        }
//        if (COST_SPARSITY && nodeCost != 0.0 && nodeCost != Double.POSITIVE_INFINITY && node.id in nnzMemo) {
//            nodeCost *= (nnzMemo[node.id]!!.toDouble() / node.schema.shapes.prod())
//            costMemo[node.id] = nodeCost
//        }
//        return nodeCost + nextNodes.sumByDouble { costSPlan(it) }
//    }

    fun costNonRec(node: SNode): Double {
        return costMemo.getOrPut(node.id) {
            when(node) {
                is SNodeAggregate -> costAgg(node)
                is SNodeNary -> costNary(node)
                else -> 0.0
            }
        }
    }

    private fun getNnz(node: SNode): Nnz = nnzInfer.infer(node)
    private fun getNnz(g: Graph): Nnz = nnzInfer.infer(g)
    private fun getNnz(b: GraphBag): Nnz = nnzInfer.infer(b)


    private fun costAgg(agg: SNodeAggregate): Double {
        if( agg.op != Hop.AggOp.SUM) // only cost SUM aggregates
            return 0.0

        // check MxM
//        val mult = agg.input
//        if( mult is SNodeNary && mult.op == SNodeNary.NaryOp.MULT
//                && mult.inputs.size == 2
//                && agg.aggs.size == 1 // todo check this - what about rowSums after MxM?
//                && mult.inputs[0].schema.names.intersect(mult.inputs[1].schema.names).first() == agg.aggs.names.first() // forbear element-wise multiplication followed by agg
//                ) {
//            var mult0 = mult.inputs[0]
//            var mult1 = mult.inputs[1]
//            // options: MxM, MxV/VxM, Inner
//            // cost of MxM is x*y*z for * and +.
//            // cost of MxV is x*y for * and +.
//            // cost of Inner is x for * and +.
//            if( mult0.schema.size == 2 && mult1.schema.size == 2) { // MxM
//
//            } else if( mult0.schema.size == 1 && mult1.schema.size == 1 ) { // Inner
//
//            } else { // MxV
//                if( mult0.schema.size == 2 && mult1.schema.size == 1 )
//                else if( mult0.schema.size == 1 && mult1.schema.size == 2 ) {
//                    mult0.let { mult0 = mult1; mult1 = it }
//                } else {
//                    return Double.POSITIVE_INFINITY
//                }
//            }
//            val flops = getNnz(mult).toDouble()
//            costMemo[mult.id] = flops // in addition to agg
//            return flops
//        }

        // general agg - sums over all data
        val aggInputNnz = getNnz(agg.input).toDouble()
        val constantAggs = agg.aggsNotInInputSchema()
        val constantAggCost = if( constantAggs.isNotEmpty() ) { // treat like multiply by constant
            aggInputNnz
        } else 0.0
        return constantAggCost + aggInputNnz
    }

    private fun costNary(nary: SNodeNary): Double {
        if (nary.op == SNodeNary.NaryOp.POW)
            return getNnz(nary).toDouble()
        if( nary.op != SNodeNary.NaryOp.MULT && nary.op != SNodeNary.NaryOp.PLUS )
            return 0.0
//        if( nary.schema.size >= 3 )
//            return 0.0 //Double.POSITIVE_INFINITY // This cost is counted by the agg above

//        if( nary.inputs.map { it.schema.names }.toSet().size == nary.inputs.size ) {
            // all schema equal; it's a big element-wise multiply/add
            // only count multiplying scalars once
            val countScalars = nary.inputs.count { it.schema.isEmpty() }
            val multiplyInputCount = nary.inputs.size - 1 - maxOf(countScalars - 1, 0)
            return multiplyInputCount * getNnz(nary).toDouble()
//        }

//        if( nary.schema.size == 2 && nary.inputs.size == 2 ) {
//            val sizes = nary.inputs.map { it.schema.size }.sorted()
//            if (sizes == listOf(1, 1)) { // Outer
//                return getNnz(nary).toDouble()
//            }
//
//            if( sizes == listOf(1, 2)) { // MeV or VeM
//                return getNnz(nary).toDouble()
//            }
//
//            if( sizes[0] == 0 ) { // multiply with constant
//                return getNnz(nary).toDouble()
//            }
//        }
//        return Double.POSITIVE_INFINITY
    }

    fun costRecUpperBound(b: GraphBag): Double {
        return getNnz(b) * (b.size - 1) + b.sumByDouble { costRecUpperBound(it) }
    }

    fun costRecUpperBound(g: Graph): Double {
        // multiply edges to big tensor, then aggregate
        val (edgesVM, edgesScalar) = g.edges.partition { it.verts.isEmpty() }
        val multFactor = edgesVM.size + if (edgesScalar.isEmpty()) 0 else 1
        val nnzBigTensor = nnzInfer.infer(g, true)
        val multCost = nnzBigTensor * multFactor
        val aggCost = if (g.aggs.isNotEmpty()) multCost else 0
        val thisCost = aggCost + multCost.toDouble()
        val belowCost = g.edges.sumByDouble { e -> when (e) {
            is Edge.C -> costRec(e.base)
            is Edge.F -> costRecUpperBound(e.base)
        } }
        return thisCost + belowCost
    }

    fun costRec(node: SNode): Double {
        return recCostMemo.getOrPut(node.id) {
            val recChildren = getChildrenAtBelow(node)
            recChildren.sumByDouble { costNonRec(it) }
        }
    }

    fun getChildrenAtBelow(node: SNode): Set<SNode> {
        if (node.inputs.isEmpty()) return setOf(node)
        return recChildrenMemo.getOrPut(node.id) {
            node.inputs.map { getChildrenAtBelow(it) }.reduce { a, b -> a+b } + node
        }
    }

    fun costRec(roots: List<SNode>): Double {
        return roots.flatMap { getChildrenAtBelow(it) }.toSet().sumByDouble { costNonRec(it) }
    }

}

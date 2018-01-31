package org.apache.sysml.hops.spoof2.enu2

import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.spoof2.plan.*

object PlanCost {
//    override fun compareTo(other: SCost): Int = flops.compareTo(other.flops)
//    operator fun plus(c: SCost) = if( c == SCost.ZERO_COST ) this else SCost(this.flops + c.flops)
//    val costMemo: MutableMap<Id, Double> = mutableMapOf()
//    val nnzMemo: MutableMap<Id, Nnz> = mutableMapOf()

//    companion object {
        private const val COST_SPARSITY = true
//    }

    // Removed in favor of calculating the cost non-recursively, due to sharing.
//    fun costSPlan(roots: List<SNode>,
//                  costMemo: MutableMap<Id, Double>, nnzMemo: MutableMap<Id, Nnz>): List<Double> {
//        if (COST_SPARSITY) {
//            NnzInfer.inferNnz(roots, nnzMemo)
//        }
//        return roots.map { costSPlan(it, costMemo, nnzMemo) }
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
//        return nodeCost + nextNodes.sumByDouble { costSPlan(it, costMemo, nnzMemo) }
//    }

    fun costNonRec(node: SNode,
                   costMemo: MutableMap<Id, Double>, nnzMemo: MutableMap<Id, Nnz>): Double {
        if (node.id in costMemo) return costMemo[node.id]!!
        val cost = when(node) {
            is SNodeAggregate -> costAgg(node, costMemo, nnzMemo)
            is SNodeNary -> costNary(node, costMemo, nnzMemo)
            else -> 0.0
        }
        costMemo[node.id] = cost
        return cost
    }

    private fun getNnz(node: SNode, nnzMemo: MutableMap<Id, Nnz>): Nnz {
        return if (COST_SPARSITY) {
            NnzInfer.inferNnz(node, nnzMemo)
        } else node.schema.shapes.prod()
    }


    private fun costAgg(agg: SNodeAggregate,
                        costMemo: MutableMap<Id, Double>, nnzMemo: MutableMap<Id, Nnz>): Double {
        if( agg.op != Hop.AggOp.SUM) // only cost SUM aggregates
            return 0.0

        // check MxM
        val mult = agg.input
        if( mult is SNodeNary && mult.op == SNodeNary.NaryOp.MULT
                && mult.inputs.size == 2
                && agg.aggs.size == 1 // todo check this - what about rowSums after MxM?
                && mult.inputs[0].schema.names.intersect(mult.inputs[1].schema.names).first() == agg.aggs.names.first() // forbear element-wise multiplication followed by agg
                ) {
            var mult0 = mult.inputs[0]
            var mult1 = mult.inputs[1]
            // options: MxM, MxV/VxM, Inner
            // cost of MxM is x*y*z for * and +.
            // cost of MxV is x*y for * and +.
            // cost of Inner is x for * and +.
            if( mult0.schema.size == 2 && mult1.schema.size == 2) { // MxM

            } else if( mult0.schema.size == 1 && mult1.schema.size == 1 ) { // Inner

            } else { // MxV
                if( mult0.schema.size == 2 && mult1.schema.size == 1 )
                else if( mult0.schema.size == 1 && mult1.schema.size == 2 ) {
                    mult0.let { mult0 = mult1; mult1 = it }
                } else {
                    return Double.POSITIVE_INFINITY
                }
            }
            val flops = getNnz(mult, nnzMemo).toDouble()
            costMemo[mult.id] = flops // in addition to agg
            return flops
        }

        // general agg - sums over all data
        val aggInputNnz = getNnz(agg.input, nnzMemo).toDouble()
        val constantAggs = agg.aggsNotInInputSchema()
        val constantAggCost = if( constantAggs.isNotEmpty() ) { // treat like multiply by constant
            aggInputNnz
        } else 0.0
        return constantAggCost + aggInputNnz
    }

    private fun costNary(nary: SNodeNary,
                         costMemo: MutableMap<Id, Double>, nnzMemo: MutableMap<Id, Nnz>): Double {
        if (nary.op == SNodeNary.NaryOp.POW)
            return getNnz(nary, nnzMemo).toDouble()
        if( nary.op != SNodeNary.NaryOp.MULT && nary.op != SNodeNary.NaryOp.PLUS )
            return 0.0
        if( nary.schema.size >= 3 )
            return Double.POSITIVE_INFINITY

        if( nary.inputs.map { it.schema.names }.toSet().size == nary.inputs.size ) {
            // all schema equal; it's a big element-wise multiply/add
            // only count multiplying scalars once
            val countScalars = nary.inputs.count { it.schema.isEmpty() }
            val multiplyInputCount = nary.inputs.size - 1 - maxOf(countScalars - 1, 0)
            return multiplyInputCount * getNnz(nary, nnzMemo).toDouble()
        }

        if( nary.schema.size == 2 && nary.inputs.size == 2 ) {
            val sizes = nary.inputs.map { it.schema.size }.sorted()
            if (sizes == listOf(1, 1)) { // Outer
                return getNnz(nary, nnzMemo).toDouble()
            }

            if( sizes == listOf(1, 2)) { // MeV or VeM
                return getNnz(nary, nnzMemo).toDouble()
            }

            if( sizes[0] == 0 ) { // multiply with constant
                return getNnz(nary, nnzMemo).toDouble()
            }
        }
        return Double.POSITIVE_INFINITY
    }

}
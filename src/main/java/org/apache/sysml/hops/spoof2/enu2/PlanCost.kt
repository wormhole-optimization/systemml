package org.apache.sysml.hops.spoof2.enu2

import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.spoof2.enu.SPCost
import org.apache.sysml.hops.spoof2.plan.*

class PlanCost {
//    override fun compareTo(other: SCost): Int = flops.compareTo(other.flops)
//    operator fun plus(c: SCost) = if( c == SCost.ZERO_COST ) this else SCost(this.flops + c.flops)
    val costMemo: MutableMap<Id, Double> = mutableMapOf()
    val nnzMemo: MutableMap<Id, Nnz> = mutableMapOf()

    companion object {
        private const val COST_SPARSITY = true
    }

    fun costSPlan(roots: List<SNode>): List<Double> {
        if (COST_SPARSITY) {
            NnzInfer.inferNnz(roots, nnzMemo)
        }
        return roots.map { costSPlan(it) }
    }

    private fun costSPlan(node: SNode): Double {
        if( node.id in costMemo )
            return costMemo[node.id]!!
        var (nextNodes, nodeCost) = when( node ) {
            is SNodeAggregate -> costAgg(node)
            is SNodeNary -> costNary(node)
            else -> node.inputs to 0.0
        }
        if (COST_SPARSITY && nodeCost != 0.0 && nodeCost != Double.POSITIVE_INFINITY && node.id in nnzMemo) {
            nodeCost *= (nnzMemo[node.id]!!.toDouble() / node.schema.shapes.prod())
            costMemo[node.id] = nodeCost
        }
        return nodeCost + nextNodes.sumByDouble { costSPlan(it) }
    }

    private fun costAgg(agg: SNodeAggregate): Pair<List<SNode>, Double> {
        if( agg.op != Hop.AggOp.SUM) // only cost SUM aggregates
            return listOf(agg.input) to 0.0

        // check MxM
        val mult = agg.input
        if( mult is SNodeNary && mult.op == SNodeNary.NaryOp.MULT
                && mult.inputs.size == 2
                && agg.aggs.size == 1
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
                    costMemo[agg.id] = Double.POSITIVE_INFINITY
                    return listOf<SNode>() to Double.POSITIVE_INFINITY
                }
            }
            val flops = mult.schema.shapes.prod().toDouble()
            costMemo[agg.id] = flops
            costMemo[mult.id] = flops
            return listOf(mult0, mult1) to flops
        }

        // general agg - sums over all data
        val constantAggs = agg.aggsNotInInputSchema()
        val constantAggCost = if( constantAggs.isNotEmpty() ) { // treat like multiply by constant
            agg.input.schema.shapes.prod().toDouble()
        } else 0.0
        val aggs = agg.aggs - constantAggs
        val cost = constantAggCost + aggs.shapes.prod().toDouble()
        costMemo[agg.id] = cost
        return listOf(agg.input) to cost
    }

    private fun costNary(nary: SNodeNary): Pair<List<SNode>, Double> {
        if (nary.op == SNodeNary.NaryOp.POW) {
            val cost = nary.schema.shapes.prod().toDouble()
            costMemo[nary.id] = cost
            return nary.inputs to cost
        }
        if( nary.op != SNodeNary.NaryOp.MULT && nary.op != SNodeNary.NaryOp.PLUS )
            return nary.inputs to 0.0

        if( nary.schema.size >= 3 ) {
            costMemo[nary.id] = Double.POSITIVE_INFINITY
            return listOf<SNode>() to Double.POSITIVE_INFINITY
        }

        if( nary.inputs.map { it.schema.names }.toSet().size == nary.inputs.size ) {
            // all schema equal; it's a big element-wise multiply/add
            val cost = nary.inputs.size * nary.inputs[0].schema.shapes.prod().toDouble()
            costMemo[nary.id] = cost
            return nary.inputs to cost
        }

        if( nary.schema.size == 2 && nary.inputs.size == 2 ) {
            val sizes = nary.inputs.map { it.schema.size }.sorted()
            if (sizes == listOf(1, 1)) { // Outer
                val cost = nary.schema.shapes.prod().toDouble()
                costMemo[nary.id] = cost
                return nary.inputs to cost
            }

            if( sizes == listOf(1, 2)) { // MeV or VeM
                val cost = nary.schema.shapes.prod().toDouble()
                costMemo[nary.id] = cost
                return nary.inputs to cost
            }

            if( sizes[0] == 0 ) { // multiply with constant
                val cost = nary.schema.shapes.prod().toDouble()
                costMemo[nary.id] = cost
                return nary.inputs to cost
            }
        }

        costMemo[nary.id] = Double.POSITIVE_INFINITY
        return listOf<SNode>() to Double.POSITIVE_INFINITY
    }

}
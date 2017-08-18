package org.apache.sysml.test.integration.functions.spoof2

import org.apache.sysml.hops.DataOp
import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.SPlanBottomUpRewriter
import org.apache.sysml.hops.spoof2.rewrite.SPlanCSEElimRewriter
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriter
import org.apache.sysml.parser.Expression
import org.apache.sysml.utils.Explain
import org.junit.Assert
import org.junit.Test

class HandTest {

    companion object {
        private fun createReadHop(name: String): DataOp {
            return DataOp(name, Expression.DataType.MATRIX, Expression.ValueType.DOUBLE, Hop.DataOpTypes.TRANSIENTREAD, "$name.csv", 3, 3, 9, 3, 3)
        }
        private fun createWriteHop(name: String): DataOp {
            return DataOp(name, Expression.DataType.MATRIX, Expression.ValueType.DOUBLE, Hop.DataOpTypes.TRANSIENTWRITE, name, 3, 3, 9, 3, 3)
        }

        private fun countAggs(roots: ArrayList<SNode>): Int {
            SNode.resetVisited(roots)
            val cnt = roots.sumBy { rCountAggs(it) }
            SNode.resetVisited(roots)
            return cnt
        }
        private fun rCountAggs(node: SNode): Int {
            if( node.visited ) // already counted
                return 0
            node.visited = true
            return when(node) {
                is SNodeAggregate -> 1 + rCountAggs(node.input)
                else -> node.inputs.sumBy { rCountAggs(it) }
            }
        }
    }

    @Test
    fun testStructureCSEElim() {

        val A = SNodeData(createReadHop("A"))
        val a = "a1"
        val b = "b2"
        val c = "c3"
        val d = "d4"
        val e = "e5"
        val ab = SNodeBind(A, mapOf(0 to a, 1 to b))
        val bc = SNodeBind(A, mapOf(0 to b, 1 to c))
        val cd = SNodeBind(A, mapOf(0 to c, 1 to d))
        val de = SNodeBind(A, mapOf(0 to d, 1 to e))
        val p = Hop.AggOp.SUM
        val m = SNodeNary.NaryOp.MULT
        val r1 = SNodeData(createWriteHop("X"),
                SNodeUnbind(
                SNodeAggregate(p, SNodeNary(m,
                SNodeAggregate(p, SNodeNary(m, ab, bc), b),
                cd
                ), c)
                , mapOf(0 to a, 1 to d))
        )
        val r2 = SNodeData(createWriteHop("Y"),
                SNodeUnbind(
                SNodeAggregate(p, SNodeNary(m,
                SNodeAggregate(p, SNodeNary(m, bc, cd), c),
                de
                ), d)
                , mapOf(0 to b, 1 to e))
        )
        val roots = arrayListOf<SNode>(r1, r2)
        System.out.print("Before:")
        System.out.println(Explain.explainSPlan(roots))

        val cseElim = SPlanCSEElimRewriter(true, true)
        var cnt = 0
        do {
            val result = cseElim.rewriteSPlan(roots)
            cnt++
        } while( result != SPlanRewriter.RewriterResult.NoChange )
        System.out.print("After (count=$cnt):")
        System.out.println(Explain.explainSPlan(roots))

        val aggs = countAggs(roots)
        Assert.assertEquals("CSE Elim should reduce the number of aggregate nodes to 2",2, aggs)

        SPlanBottomUpRewriter().rewriteSPlan(roots)
        System.out.print("After Bind Unify:")
        System.out.println(Explain.explainSPlan(roots))
    }



}
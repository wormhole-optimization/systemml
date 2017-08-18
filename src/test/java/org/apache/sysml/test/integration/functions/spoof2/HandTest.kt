package org.apache.sysml.test.integration.functions.spoof2

import org.apache.sysml.hops.DataOp
import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.rewrite.HopRewriteUtils
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.SPlanCSEElimRewriter
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriter
import org.apache.sysml.parser.Expression
import org.apache.sysml.utils.Explain
import org.junit.Test

class HandTest {


    @Test
    fun testStructureCSEElim() {

        val A = SNodeData(DataOp("A", Expression.DataType.MATRIX, Expression.ValueType.DOUBLE, Hop.DataOpTypes.TRANSIENTREAD, "A.csv", 3, 3, 9, 3, 3))
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
        val r1 = SNodeAggregate(p, SNodeNary(m,
                SNodeAggregate(p, SNodeNary(m, ab, bc), b),
                cd
                ), c)
        val r2 = SNodeAggregate(p, SNodeNary(m,
                SNodeAggregate(p, SNodeNary(m, bc, cd), c),
                de
                ), d)
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

    }


}
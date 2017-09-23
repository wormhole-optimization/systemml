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

    }

//    @Test
//    fun testCompare() {
//        println(false < true)
//    }

    private val A = SNodeData(createReadHop("A"))
    private val a = AB() //"a1"
    private val b = AB() //"b2"
    private val c = AB() //"c3"
    private val d = AB() //"d4"
    private val e = AB() //"e5"
    private val p = Hop.AggOp.SUM
    private val m = SNodeNary.NaryOp.MULT

    @Test
    fun testStructureCSEElim_AAA() {
        val ab = SNodeBind(A, mapOf(AU.U0 to a, AU.U1 to b))
        val bc = SNodeBind(A, mapOf(AU.U0 to b, AU.U1 to c))
        val cd = SNodeBind(A, mapOf(AU.U0 to c, AU.U1 to d))
        val de = SNodeBind(A, mapOf(AU.U0 to d, AU.U1 to e))
        val r1 = SNodeData(createWriteHop("X"),
                SNodeUnbind(
                SNodeAggregate(p, SNodeNary(m,
                SNodeAggregate(p, SNodeNary(m, ab, bc), b),
                cd
                ), c)
                , mapOf(AU.U0 to a, AU.U1 to d))
        )
        val r2 = SNodeData(createWriteHop("Y"),
                SNodeUnbind(
                SNodeAggregate(p, SNodeNary(m,
                SNodeAggregate(p, SNodeNary(m, bc, cd), c),
                de
                ), d)
                , mapOf(AU.U0 to b, AU.U1 to e))
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

        val aggs = countPred(roots) { it is SNodeAggregate }
        Assert.assertEquals("CSE Elim should reduce the number of aggregate nodes to 2",2, aggs)

        SPlanBottomUpRewriter().rewriteSPlan(roots)
        System.out.print("After Bind Unify:")
        System.out.println(Explain.explainSPlan(roots))
    }


    /**
     * Should not unify A %*% B with B %*% A; these are different expressions.
     */
    @Test
    fun testStructureCSEElim_AB_BA() {
        val A = SNodeData(createReadHop("A"))
        val B = SNodeData(createReadHop("B"))
        val ab = SNodeBind(A, mapOf(AU.U0 to a, AU.U1 to b))
        val bc = SNodeBind(B, mapOf(AU.U0 to b, AU.U1 to c))
        val cd = SNodeBind(B, mapOf(AU.U0 to c, AU.U1 to d))
        val de = SNodeBind(A, mapOf(AU.U0 to d, AU.U1 to e))
        val AB = SNodeAggregate(p,
                    SNodeNary(m, ab, bc)
                , b)
        val BA = SNodeAggregate(p,
                    SNodeNary(m, cd, de)
                , d)
        val roots = arrayListOf<SNode>(AB, BA)
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

        SPlanBottomUpRewriter().rewriteSPlan(roots)
        SPlanBottomUpRewriter().rewriteSPlan(roots)
        System.out.print("After Bind Unify:")
        System.out.println(Explain.explainSPlan(roots))

        val aggs = countPred(roots) { it is SNodeAggregate }
        val nary = countPred(roots) { it is SNodeNary }
        Assert.assertEquals("CSE Elim should not unify AB and BA",2, aggs)
        Assert.assertEquals("CSE Elim should not unify AB and BA",2, nary)
    }



}
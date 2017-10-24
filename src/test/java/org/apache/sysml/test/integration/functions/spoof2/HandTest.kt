package org.apache.sysml.test.integration.functions.spoof2

import org.apache.sysml.hops.DataOp
import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.spoof2.SPlanCseEliminator
import org.apache.sysml.hops.spoof2.enu.RewriteSplitBU_ExtendNormalForm
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.*
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

    @Test
    fun testStructureCSEElim_AAA() {
        val A = SNodeData(createReadHop("A"))
        val a = AB() //"a1"
        val b = AB() //"b2"
        val c = AB() //"c3"
        val d = AB() //"d4"
        val e = AB() //"e5"
        val p = Hop.AggOp.SUM
        val m = SNodeNary.NaryOp.MULT

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

        var cnt = 0
        do {
            val result = SPlanCseEliminator.rewriteSPlan(roots, SPlanCseEliminator.Params())
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
        val a = AB() //"a1"
        val b = AB() //"b2"
        val c = AB() //"c3"
        val d = AB() //"d4"
        val e = AB() //"e5"
        val p = Hop.AggOp.SUM
        val m = SNodeNary.NaryOp.MULT

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

        var cnt = 0
        do {
            val result = SPlanCseEliminator.rewriteSPlan(roots, SPlanCseEliminator.Params())
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

    @Test
    fun testRewriteSplitBU() {
        val A = SNodeData(createReadHop("A"))
        AB() // start with id 1
        val a1 = AB()
        val a2 = AB()
        val a3 = AB()
        val s = Hop.AggOp.SUM
        val m = SNodeNary.NaryOp.MULT
        val p = SNodeNary.NaryOp.PLUS

        val ab = SNodeBind(A, mapOf(AU.U0 to a1, AU.U1 to a2))
        val ab_cs = SNodeAggregate(s, ab, a1)
        val a_p_cs = SNodeNary(p, ab, ab_cs) //1,2 * 1,3
        val u1 = SNodeUnbind(a_p_cs, mapOf(AU.U0 to a2))
        val b1 = SNodeBind(u1, mapOf(AU.U0 to a3))
        val tm = SNodeNary(m, b1, a_p_cs)
        val tma = SNodeAggregate(s, tm, a1)
        val uf = SNodeUnbind(tma, mapOf(AU.U0 to a2, AU.U1 to a3))
        val w = SNodeData(createWriteHop("R"), uf)
        val roots = arrayListOf<SNode>(w)

        println("orig: ")
        println(Explain.explainSPlan(roots))
        SPlanValidator.validateSPlan(roots)

        val rewriter = SPlanNormalFormRewriter()
        val toNF = listOf(
                RewriteSplitCSE(),          // split CSEs when they would block a sum-product rearrangement
//                RewritePullAggAboveMult(),
//                RewriteAggregateElim(),
//                RewriteMultiplyPlusElim(),
                RewritePullPlusAboveMult()
//                RewritePushAggIntoPlus()
//            RewritePullAggAbovePlus()
        )
//        val rsbu = RewriteSplitBU_ExtendNormalForm()

        rewriter.rewriteDown(roots, toNF)
//        rewriter.rewriteDown(roots, rsbu)

        println("new: ")
        println(Explain.explainSPlan(roots))
        SPlanValidator.validateSPlan(roots)
    }



}
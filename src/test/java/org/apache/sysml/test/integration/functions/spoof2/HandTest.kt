package org.apache.sysml.test.integration.functions.spoof2

import org.apache.sysml.hops.DataOp
import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.spoof2.NormalFormHash
import org.apache.sysml.hops.spoof2.SPlan2NormalForm
import org.apache.sysml.hops.spoof2.SPlanCseEliminator
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.*
import org.apache.sysml.parser.Expression
import org.apache.sysml.utils.Explain
import org.junit.Assert
import org.junit.Test
import java.util.Comparator
import kotlin.test.assertEquals

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

        SPlanBottomUpRewriter.rewriteSPlan(roots)
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

        SPlanBottomUpRewriter.rewriteSPlan(roots)
        SPlanBottomUpRewriter.rewriteSPlan(roots)
        System.out.print("After Bind Unify:")
        System.out.println(Explain.explainSPlan(roots))

        val aggs = countPred(roots) { it is SNodeAggregate }
        val nary = countPred(roots) { it is SNodeNary }
        Assert.assertEquals("CSE Elim should not unify AB and BA",2, aggs)
        Assert.assertEquals("CSE Elim should not unify AB and BA",2, nary)
    }

    /**
     * Test that an agg-multiply with inputs A, B hashes to the same value as one with inputs B, A.
     */
    @Test
    fun testHash_AB_BA() {
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
        val cd = SNodeBind(A, mapOf(AU.U0 to c, AU.U1 to d))
        val de = SNodeBind(B, mapOf(AU.U0 to d, AU.U1 to e))
        val AB = SNodeAggregate(p,
                SNodeNary(m, ab, bc)
                , b)
        val BA = SNodeAggregate(p,
                SNodeNary(m, de, cd)
                , d)

        System.out.println("Explain1: "+Explain.explain(AB))
        AB.resetVisited()
        System.out.println("Explain2: "+Explain.explain(BA))
        BA.resetVisited()
        val hash1 = NormalFormHash.hashNormalForm(AB)
        val hash2 = NormalFormHash.hashNormalForm(BA)
        System.out.println("Explain1: "+Explain.explain(AB))
        AB.resetVisited()
        System.out.println("Explain2: "+Explain.explain(BA))
        BA.resetVisited()
        assertEquals(hash1, hash2)
    }

    /**
     * Test that AB*AB hashes the same no matter how we switch values around.
     */
    @Test
    fun testHash_ABxBA() {
        val A = SNodeData(createReadHop("A"))
        val B = SNodeData(createReadHop("B"))
        val a = AB() //"a1"
        val b = AB() //"b2"
        val c = AB() //"c3"
        val d = AB() //"d4"
        val p = Hop.AggOp.SUM
        val m = SNodeNary.NaryOp.MULT

        val ab = SNodeBind(A, mapOf(AU.U0 to a, AU.U1 to b))
        val bc = SNodeBind(B, mapOf(AU.U0 to b, AU.U1 to c))
        val ad = SNodeBind(A, mapOf(AU.U0 to a, AU.U1 to d))
        val dc = SNodeBind(B, mapOf(AU.U0 to d, AU.U1 to c))
        val AB = SNodeAggregate(p,
                SNodeNary(m, ab, bc)
                , b)
        val BA = SNodeAggregate(p,
                SNodeNary(m, dc, ad)
                , d)
        val ABxBA = SNodeNary(m, AB, BA)
        val BAxAB = SNodeNary(m, BA, AB)

        listOf(AB to BA, ABxBA to BAxAB).forEach { (n1, n2) ->
            testHash(n1, n2)
        }

//        System.out.println("Explain1: "+Explain.explain(AB))
//        AB.resetVisited()
//        System.out.println("Explain2: "+Explain.explain(BA))
//        BA.resetVisited()

        val w1 = SNodeData(createWriteHop("w1"), SNodeUnbind(ABxBA, mapOf(AU.U0 to a, AU.U1 to c)))
        val w2 = SNodeData(createWriteHop("w2"), SNodeUnbind(BAxAB, mapOf(AU.U0 to a, AU.U1 to c)))
        val roots = arrayListOf<SNode>(w1, w2)

        println(Explain.explainSPlan(roots))
        SPlan2NormalForm.rewriteSPlan(roots)

        testHash(w1.inputs[0], w2.inputs[0])
        println(Explain.explainSPlan(roots))
    }
    // todo test the case of independent connected components

    private fun testHash(n1: SNode, n2: SNode) {
        val s1 = NormalFormHash.prettyPrintByPosition(n1)
        val s2 = NormalFormHash.prettyPrintByPosition(n2)
        val h1 = NormalFormHash.hashNormalForm(n1)
        val h2 = NormalFormHash.hashNormalForm(n2)
        println(s1)
        assertEquals(s1, s2)
        assertEquals(h1, h2)
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

        SPlanTopDownRewriter.rewriteDown(roots, toNF)
//        rewriter.rewriteDown(roots, rsbu)

        println("new: ")
        println(Explain.explainSPlan(roots))
        SPlanValidator.validateSPlan(roots)
    }


    @Test
    fun testSortHierarchical() {
        val data = listOf(
                Triple(11, 21, 31),
                Triple(10, 20, 30),
                Triple(11, 21, 30),
                Triple(11, 20, 30)
        )
        val sortFuns = listOf<(Triple<Int,Int,Int>) -> Int>(
                { it.first },
                { it.second },
                { it.third }
        )
        val sortIdxs = NormalFormHash.sortIndicesHierarchical(data, sortFuns)
        assertEquals(listOf(1, 3, 2, 0), sortIdxs)
        val actual = data.permute(sortIdxs)
        val expected = data.sortedWith(compareTriple())
        assertEquals(expected, actual)
    }

    private fun <A:Comparable<A>,B:Comparable<B>,C:Comparable<C>> compareTriple(): Comparator<Triple<A,B,C>> {
        return Comparator.comparing<Triple<A,B,C>,A> {it.first}.thenComparing<B> {it.second}.thenComparing<C> {it.third}
    }


}
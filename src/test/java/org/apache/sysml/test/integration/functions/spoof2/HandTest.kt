package org.apache.sysml.test.integration.functions.spoof2

import org.apache.sysml.hops.DataOp
import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.spoof2.SHash
import org.apache.sysml.hops.spoof2.SPlan2NormalForm
import org.apache.sysml.hops.spoof2.SPlanCseEliminator
import org.apache.sysml.hops.spoof2.enu2.SPlanEnumerate
import org.apache.sysml.hops.spoof2.enu2.SPlanEnumerate3
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.*
import org.apache.sysml.parser.Expression
import org.apache.sysml.utils.Explain
import org.junit.Assert
import org.junit.Test
import java.util.*
import kotlin.test.assertEquals
import kotlin.test.assertTrue

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
        println(Explain.explainSPlan(roots))

        var cnt = 0
        do {
            val result = SPlanCseEliminator.rewriteSPlan(roots, SPlanCseEliminator.Params())
            cnt++
        } while( result != SPlanRewriter.RewriterResult.NoChange )
        System.out.print("After (count=$cnt):")
        println(Explain.explainSPlan(roots))

        val aggs = countPred(roots) { it is SNodeAggregate }
        Assert.assertEquals("CSE Elim should reduce the number of aggregate nodes to 2",2, aggs)

        SPlanBottomUpRewriter.rewriteSPlan(roots)
        System.out.print("After Bind Unify:")
        println(Explain.explainSPlan(roots))
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
        println(Explain.explainSPlan(roots))

        var cnt = 0
        do {
            val result = SPlanCseEliminator.rewriteSPlan(roots, SPlanCseEliminator.Params())
            cnt++
        } while( result != SPlanRewriter.RewriterResult.NoChange )
        System.out.print("After (count=$cnt):")
        println(Explain.explainSPlan(roots))

        SPlanBottomUpRewriter.rewriteSPlan(roots)
        SPlanBottomUpRewriter.rewriteSPlan(roots)
        System.out.print("After Bind Unify:")
        println(Explain.explainSPlan(roots))

        val aggs = countPred(roots) { it is SNodeAggregate }
        val nary = countPred(roots) { it is SNodeNary }
        Assert.assertEquals("CSE Elim should not unify AB and BA",2, aggs)
        Assert.assertEquals("CSE Elim should not unify AB and BA",2, nary)
    }

    /**
     * Test that an agg-multiply with inputs A, B hashes to the same value as one with inputs B, A.
     * Also tests a small part of SPlanEnumerate.
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

        println("Explain1: "+Explain.explain(AB))
        AB.resetVisited()
        println("Explain2: "+Explain.explain(BA))
        BA.resetVisited()
        val hash1 = SHash.hash(AB)
        val hash2 = SHash.hash(BA)
        println("Explain1: "+Explain.explain(AB))
        AB.resetVisited()
        println("Explain2: "+Explain.explain(BA))
        BA.resetVisited()
        assertEquals(hash1, hash2)

        val r0 = SNodeData(createWriteHop("r0"),
                SNodeUnbind(AB, mapOf(AU.U0 to a, AU.U1 to c)))
        val r1 = SNodeData(createWriteHop("r1"),
                SNodeUnbind(BA, mapOf(AU.U0 to c, AU.U1 to e)))
        val roots = listOf(r0, r1)
        println("Explain before enu: "+Explain.explainSPlan(roots))
        val enu = SPlanEnumerate(roots)
        enu.expandAll()
        println("Explain after enu : "+Explain.explainSPlan(roots))
        val aggs = countPred(roots) { it is SNodeAggregate }
        val nary = countPred(roots) { it is SNodeNary }
        Assert.assertEquals("Plan Enumeration should unify semantically equivalent sub-expressions",1, aggs)
        Assert.assertEquals("Plan Enumeration should unify semantically equivalent sub-expressions",1, nary)
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

//        println("Explain1: "+Explain.explain(AB))
//        AB.resetVisited()
//        println("Explain2: "+Explain.explain(BA))
//        BA.resetVisited()

        val w1 = SNodeData(createWriteHop("w1"), SNodeUnbind(ABxBA, mapOf(AU.U0 to a, AU.U1 to c)))
        val w2 = SNodeData(createWriteHop("w2"), SNodeUnbind(BAxAB, mapOf(AU.U0 to a, AU.U1 to c)))
        val roots = arrayListOf<SNode>(w1, w2)

        println(Explain.explainSPlan(roots))
        SPlan2NormalForm.rewriteSPlan(roots)

        testHash(w1.inputs[0], w2.inputs[0])

        println("Explain before enu: "+Explain.explainSPlan(roots))
        val enu = SPlanEnumerate3(roots)
        enu.expandAll()
        println("Explain after enu : "+Explain.explainSPlan(roots))
        val aggs = countPred(roots) { it is SNodeAggregate }
        val nary = countPred(roots) { it is SNodeNary }
        Assert.assertEquals("Plan Enumeration should unify semantically equivalent sub-expressions",1, aggs)
        Assert.assertEquals("Plan Enumeration should unify semantically equivalent sub-expressions",2, nary)
    }
    // todo test the case of independent connected components

    private fun testHash(n1: SNode, n2: SNode) {
        val s1 = SHash.prettyPrintByPosition(n1)
        val s2 = SHash.prettyPrintByPosition(n2)
        val h1 = SHash.hash(n1)
        val h2 = SHash.hash(n2)
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
                Triple(11, 20, 30),
                Triple(11, 21, 31)
        )
        val sortFuns = listOf<(Triple<Int,Int,Int>) -> Int>(
                { it.first },
                { it.second },
                { it.third }
        )
        val stillConfused = mutableListOf<SHash.IntSlice>()
        val sortIdxs = SHash.sortIndicesHierarchical(data, sortFuns, stillConfused)
        assertEquals(listOf(1, 3, 2, 0, 4), sortIdxs)
        val actual = data.permute(sortIdxs)
        val expected = data.sortedWith(compareTriple())
        assertEquals(expected, actual)
        assertEquals(listOf(SHash.IntSlice(3, 4)), stillConfused)
    }

    private fun <A:Comparable<A>,B:Comparable<B>,C:Comparable<C>> compareTriple(): Comparator<Triple<A,B,C>> {
        return Comparator.comparing<Triple<A,B,C>,A> {it.first}.thenComparing<B> {it.second}.thenComparing<C> {it.third}
    }

    /**
     * Test [SHash.sortIndicesHierarchical] on randomly generated lists of data.
     */
    @Test
    fun testRandomSortHierarchical() {
        val seed = System.currentTimeMillis()
        println("seed is $seed")
        val r = Random(seed)

        // dimension is RANGES.size
        val RANGES = listOf(
                SHash.IntSlice(10, 15),
                SHash.IntSlice(20, 25),
                SHash.IntSlice(30, 35)
        )
        val NUM_POINTS = 50

        val data: MutableList<List<Int>> = mutableListOf()
        repeat(NUM_POINTS) {
            val list = mutableListOf<Int>()
            for (range in RANGES) {
                list += r.nextInt(range.last-range.first+1) + range.first // [10,15]
            }
            data += list
        }

        val sortFuns: MutableList<(List<Int>) -> Int> = mutableListOf()
        for (i in RANGES.indices) {
            sortFuns += { it[i] }
        }

        val stillConfused = mutableListOf<SHash.IntSlice>()
        val sortIdxs = SHash.sortIndicesHierarchical(data, sortFuns, stillConfused)
        val actual = data.permute(sortIdxs)
        val expect = data.sortedWith(listComparator())
        assertEquals(expect, actual)
//        println(stillConfused.map { it.map { data[sortIdxs[it]] } })
        stillConfused.forEach { sc ->
            val d = data[sortIdxs[sc.first]]
            assertTrue((sc.first+1..sc.last).all { data[sortIdxs[it]] == d })
        }
    }

    private fun <T : Comparable<T>> listComparator(): Comparator<List<T>> {
        return Comparator { a, b ->
            val min = minOf(a.size, b.size)
            var i = 0
            var c = 0
            while( c == 0 && i < min ) {
                c = a[i].compareTo(b[i])
                i++
            }
            if( c == 0 ) a.size.compareTo(b.size)
            else c
        }
    }


}
package org.apache.sysml.test.integration.functions.spoof2

import org.apache.sysml.hops.DataOp
import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.LiteralOp
import org.apache.sysml.hops.spoof2.SHash
import org.apache.sysml.hops.spoof2.SPlan2NormalForm_InsertStyle
import org.apache.sysml.hops.spoof2.SPlanCseEliminator
import org.apache.sysml.hops.spoof2.enu2.*
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.*
import org.apache.sysml.parser.Expression
import org.apache.sysml.utils.Explain
import org.junit.Assert
import org.junit.Assume
import org.junit.Test
import java.util.*
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class HandTest {

    companion object {
        private fun createReadHop(name: String, r: Long = 3, c: Long = 3): DataOp {
            return DataOp(name, Expression.DataType.MATRIX, Expression.ValueType.DOUBLE, Hop.DataOpTypes.TRANSIENTREAD, "$name.csv", r, c, 9, 3, 3)
        }
        private fun createWriteHop(name: String): DataOp {
            return DataOp(name, Expression.DataType.MATRIX, Expression.ValueType.DOUBLE, Hop.DataOpTypes.TRANSIENTWRITE, name, 3, 3, 9, 3, 3)
        }
        private fun extractOrNodes(node: SNode, orNodes: MutableSet<OrNode> = mutableSetOf()): Set<OrNode> {
            if (node.visited) return orNodes
            node.visited = true
            if (node is OrNode) orNodes += node
            node.inputs.forEach { extractOrNodes(it, orNodes) }
            return orNodes
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
            val result = SPlanCseEliminator.rewriteSPlan(roots, SPlanCseEliminator.Params(true))
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
        val enu = SPlanEnumerate3(roots)
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
        SPlan2NormalForm_InsertStyle(true).rewriteSPlan(roots)

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


    /**
     * Test that AB*AB hashes the same no matter how we switch values around.
     */
    @Test
    fun testUVUV() {
        val A = SNodeData(createReadHop("U"))
        val B = SNodeData(createReadHop("V"))
        val i = AB() //"a1"
        val j = AB() //"b2"
        val k = AB() //"c3"
        val l= AB() //"d4"
        val p = Hop.AggOp.SUM
        val m = SNodeNary.NaryOp.MULT

        val ij = SNodeBind(A, mapOf(AU.U0 to i, AU.U1 to j))
        val ik = SNodeBind(A, mapOf(AU.U0 to i, AU.U1 to k)) // also try A B A B
        val lk = SNodeBind(B, mapOf(AU.U0 to l, AU.U1 to k))
        val lj = SNodeBind(B, mapOf(AU.U0 to l, AU.U1 to j))
        val UVj = SNodeAggregate(p,
                SNodeNary(m, ij, lj)
                , j)
        val UVk = SNodeAggregate(p,
                SNodeNary(m, ik, lk)
                , k)
        val UVUV1 = SNodeNary(m, UVj, UVk)
        val UVUV2 = SNodeNary(m, UVk, UVj)

//        listOf(UVj to UVk, UVUV1 to UVUV2).forEach { (n1, n2) ->
//            testHash(n1, n2)
//        }

//        println("Explain1: "+Explain.explain(AB))
//        AB.resetVisited()
//        println("Explain2: "+Explain.explain(BA))
//        BA.resetVisited()

//        val w1 = SNodeData(createWriteHop("w1"), SNodeUnbind(UVUV1, mapOf(AU.U0 to i, AU.U1 to l)))
//        val w2 = SNodeData(createWriteHop("w2"), SNodeUnbind(UVUV2, mapOf(AU.U0 to i, AU.U1 to l)))
//        val roots = arrayListOf<SNode>(w1, w2)
        val sum1 = SNodeAggregate(Hop.AggOp.SUM, UVUV1, i, l)
        val sum2 = SNodeAggregate(Hop.AggOp.SUM, UVUV2, i, l)
        val w1 = SNodeData(createWriteHop("w1"), sum1)
        val w2 = SNodeData(createWriteHop("w2"), sum2)
        val roots = arrayListOf<SNode>(w1, w2)

        println(Explain.explainSPlan(roots))
        SPlan2NormalForm_InsertStyle(true).rewriteSPlan(roots)

//        testHash(w1.inputs[0], w2.inputs[0]) // todo test GraphCanonizer

        println("Explain before enu: "+Explain.explainSPlan(roots))
        val enu = SPlanEnumerate3(roots)
        enu.expandAll()
        println("Explain after enu : "+Explain.explainSPlan(roots))
        val aggs = countPred(roots) { it is SNodeAggregate }
        val nary = countPred(roots) { it is SNodeNary }
        println("result aggs nary: $aggs $nary")
//        Assert.assertEquals("Plan Enumeration should unify semantically equivalent sub-expressions",1, aggs)
//        Assert.assertEquals("Plan Enumeration should unify semantically equivalent sub-expressions",2, nary)
    }

    /**
     * Test ABC
     */
    @Test
    fun testABC() {
        val A = SNodeData(createReadHop("A"))
        val B = SNodeData(createReadHop("B"))
        val C = SNodeData(createReadHop("C"))
        val a = AB() //"a1"
        val b = AB() //"b2"
        val c = AB() //"c3"
        val d = AB() //"d4"
        val p = Hop.AggOp.SUM
        val m = SNodeNary.NaryOp.MULT

        val ab = SNodeBind(A, mapOf(AU.U0 to a, AU.U1 to b))
        val bc = SNodeBind(B, mapOf(AU.U0 to b, AU.U1 to c))
        val cd = SNodeBind(C, mapOf(AU.U0 to c, AU.U1 to d))
        val AB = SNodeAggregate(p,
                SNodeNary(m, ab, bc), b)
        val ABC = SNodeAggregate(p,
                SNodeNary(m, AB, cd), c)

//        listOf(UVj to UVk, UVUV1 to UVUV2).forEach { (n1, n2) ->
//            testHash(n1, n2)
//        }
//        println("Explain1: "+Explain.explain(AB))
//        AB.resetVisited()

        val w1 = SNodeData(createWriteHop("w1"), SNodeUnbind(ABC, mapOf(AU.U0 to a, AU.U1 to d)))
        val roots = arrayListOf<SNode>(w1)

        println(Explain.explainSPlan(roots))
        SPlan2NormalForm_InsertStyle(true).rewriteSPlan(roots)

//        testHash(w1.inputs[0], w2.inputs[0]) // todo test GraphCanonizer

        println("Explain before enu: "+Explain.explainSPlan(roots))
        val enu = SPlanEnumerate3(roots)
        enu.expandAll()
        println("Explain after enu : "+Explain.explainSPlan(roots))
        val aggs = countPred(roots) { it is SNodeAggregate }
        val nary = countPred(roots) { it is SNodeNary }
        println("result aggs nary: $aggs $nary")
        Assume.assumeFalse(SPlanEnumerate3.UNSOUND_PRUNE_LOCAL_BYCOST)
        Assert.assertEquals(4, aggs)
        Assert.assertEquals(4, nary)
    }

    @Test
    fun testABC_BCD() {
        val A = SNodeData(createReadHop("A"))
        val B = SNodeData(createReadHop("B"))
        val C = SNodeData(createReadHop("C"))
        val D = SNodeData(createReadHop("D"))
        val a = AB() //"a1"
        val b = AB() //"b2"
        val c = AB() //"c3"
        val d = AB() //"d4"
        val p = Hop.AggOp.SUM
        val m = SNodeNary.NaryOp.MULT

        val ab = SNodeBind(A, mapOf(AU.U0 to a, AU.U1 to b))
        val bc = SNodeBind(B, mapOf(AU.U0 to b, AU.U1 to c))
        val cd = SNodeBind(C, mapOf(AU.U0 to c, AU.U1 to d))
        val abB = SNodeBind(B, mapOf(AU.U0 to a, AU.U1 to b))
        val bdC = SNodeBind(C, mapOf(AU.U0 to b, AU.U1 to d))
        val dcD = SNodeBind(D, mapOf(AU.U0 to d, AU.U1 to c))
        val AB = SNodeAggregate(p,
                SNodeNary(m, ab, bc), b)
        val ABC = SNodeAggregate(p,
                SNodeNary(m, AB, cd), c)
        val BC = SNodeAggregate(p,
                SNodeNary(m, abB, bdC), b)
        val BCD = SNodeAggregate(p,
                SNodeNary(m, BC, dcD), d)
//        listOf(UVj to UVk, UVUV1 to UVUV2).forEach { (n1, n2) ->
//            testHash(n1, n2)
//        }
//        println("Explain1: "+Explain.explain(AB))
//        AB.resetVisited()

        val w1 = SNodeData(createWriteHop("w1"), SNodeUnbind(ABC, mapOf(AU.U0 to a, AU.U1 to d)))
        val w2 = SNodeData(createWriteHop("w2"), SNodeUnbind(BCD, mapOf(AU.U0 to a, AU.U1 to c)))
        val roots = arrayListOf<SNode>(w1, w2)

        println(Explain.explainSPlan(roots))
        SPlan2NormalForm_InsertStyle(true).rewriteSPlan(roots)

//        testHash(w1.inputs[0], w2.inputs[0]) // todo test GraphCanonizer

        println("Explain before enu: "+Explain.explainSPlan(roots))
        val enu = SPlanEnumerate3(roots)
        enu.expandAll()
        println("Explain after enu : "+Explain.explainSPlan(roots))
        val aggs = countPred(roots) { it is SNodeAggregate }
        val nary = countPred(roots) { it is SNodeNary }
        println("result aggs nary: $aggs $nary")
        Assume.assumeFalse(SPlanEnumerate3.UNSOUND_PRUNE_LOCAL_BYCOST)
        Assert.assertEquals(7, aggs)
        Assert.assertEquals(7, nary)
    }

    @Test
    fun testABC_plus_DBC() {
        val A = SNodeData(createReadHop("A"))
        val B = SNodeData(createReadHop("B"))
        val C = SNodeData(createReadHop("C"))
        val D = SNodeData(createReadHop("D"))
        val a = AB() //"a1"
        val b = AB() //"b2"
        val c = AB() //"c3"
        val d = AB() //"c3"
        val x = AB() //"d4"
        val y = AB() //"d4"
        val p = Hop.AggOp.SUM
        val m = SNodeNary.NaryOp.MULT

        val ab = SNodeBind(A, mapOf(AU.U0 to a, AU.U1 to b))
        val bc = SNodeBind(B, mapOf(AU.U0 to b, AU.U1 to c))
        val cd = SNodeBind(C, mapOf(AU.U0 to c, AU.U1 to d))
        val ax = SNodeBind(D, mapOf(AU.U0 to a, AU.U1 to x))
        val xy = SNodeBind(B, mapOf(AU.U0 to x, AU.U1 to y))
        val yd = SNodeBind(C, mapOf(AU.U0 to y, AU.U1 to d))
        val AB = SNodeAggregate(p,
                SNodeNary(m, ab, bc), b)
        val ABC = SNodeAggregate(p,
                SNodeNary(m, AB, cd), c)
        val DB = SNodeAggregate(p,
                SNodeNary(m, ax, xy), x)
        val DBC = SNodeAggregate(p,
                SNodeNary(m, DB, yd), y)
        val ABCDBC = SNodeNary(SNodeNary.NaryOp.PLUS, ABC, DBC)

        val w1 = SNodeData(createWriteHop("w1"), SNodeUnbind(ABCDBC, mapOf(AU.U0 to a, AU.U1 to d)))
        val roots = arrayListOf<SNode>(w1)

        println(Explain.explainSPlan(roots))
        SPlan2NormalForm_InsertStyle(true).rewriteSPlan(roots)

        println("Explain before enu: "+Explain.explainSPlan(roots))
        val enu = SPlanEnumerate3(roots)
        enu.expandAll()
        println("Explain after enu : "+Explain.explainSPlan(roots))
        val aggs = countPred(roots) { it is SNodeAggregate }
        val nary = countPred(roots) { it is SNodeNary }
        println("result aggs nary: $aggs $nary")
//        Assert.assertEquals(7, aggs)
//        Assert.assertEquals(7, nary)
    }

    @Test
    fun testAAA() {
        val A = SNodeData(createReadHop("A"))
        val a = AB() //"a1"
        val b = AB() //"b2"
        val p = Hop.AggOp.SUM
        val m = SNodeNary.NaryOp.MULT

        val ab = SNodeBind(A, mapOf(AU.U0 to a, AU.U1 to b))
        val AAA = SNodeNary(SNodeNary.NaryOp.PLUS, ab, ab, ab)

        val w1 = SNodeData(createWriteHop("w1"), SNodeUnbind(AAA, mapOf(AU.U0 to a, AU.U1 to b)))
        val roots = arrayListOf<SNode>(w1)

        println(Explain.explainSPlan(roots))
        SPlan2NormalForm_InsertStyle(true).rewriteSPlan(roots)

        println("Explain before enu: "+Explain.explainSPlan(roots))
        val enu = SPlanEnumerate3(roots)
        enu.expandAll()
        println("Explain after enu : "+Explain.explainSPlan(roots))
        val aggs = countPred(roots) { it is SNodeAggregate }
        val nary = countPred(roots) { it is SNodeNary }
        println("result aggs nary: $aggs $nary")
//        Assert.assertEquals(7, aggs)
//        Assert.assertEquals(7, nary)

        w1.resetVisited()
        val orNodes = extractOrNodes(w1)
        Assume.assumeTrue(orNodes.size == 1)
        val orNode = orNodes.single()
        assertEquals(3, orNode.inputs.size, "redundant factorings enumerated") // todo
    }


    /**
     * Test that AB*AB hashes the same no matter how we switch values around.
     */
    @Test
    fun testUVUV_CanonGraph() {
        val U = SNodeData(createReadHop("U"))
        val V = SNodeData(createReadHop("V"))
        val a7 = ABS(AB(), 9) //7
        val a2 = ABS(AB(), 9) //2
        val a3 = ABS(AB(), 9) //3
        val a8 = ABS(AB(), 9) //8

        val U72 = Edge.C(U, listOf(a7,a2)) //SNodeBind(U, mapOf(AU.U0 to a7, AU.U1 to a2)) // U 7,2
        val U73 = Edge.C(U, listOf(a7,a3)) //SNodeBind(U, mapOf(AU.U0 to a7, AU.U1 to a3)) // U 7,3
        val V83 = Edge.C(V, listOf(a8,a3)) //SNodeBind(V, mapOf(AU.U0 to a8, AU.U1 to a3)) // V 8,3
        val V82 = Edge.C(V, listOf(a8,a2)) //SNodeBind(V, mapOf(AU.U0 to a8, AU.U1 to a2)) // V 8,2
        val g1 = Graph(setOf(a7,a2), listOf(U72, V82, U73, V83))
        val g2 = Graph(setOf(a7,a3), listOf(U72, V82, U73, V83))

        val memo = CanonMemo()
        val c1 = memo.canonize(g1)
        val c2 = memo.canonize(g2)
        assertEquals(c1.rep, c2.rep)
    }


    @Test
    fun testMultOrderBySparsity() {
        val A = SNodeData(createReadHop("A"))
        val B = SNodeData(createReadHop("B"))
        val u1 = SNodeData(createReadHop("u", 1, 3))
        val u2 = SNodeData(createReadHop("u", 1, 3))
        val v1 = SNodeData(createReadHop("v", 1, 3))
        val v2 = SNodeData(createReadHop("v", 1, 3))
        val w1 = SNodeData(createReadHop("w", 1, 3))
        val w2 = SNodeData(createReadHop("w", 1, 3))
        val z1 = SNodeData(LiteralOp(2.5))
        val z2 = SNodeData(LiteralOp(3.5))
        val a = AB() //"a1"
        val b = AB() //"b2"
        val c = AB() //"c3"

        val Aab = SNodeBind(A, mapOf(AU.U0 to a, AU.U1 to b))
        val Bbc = SNodeBind(B, mapOf(AU.U0 to b, AU.U1 to c))
        val u1a = SNodeBind(u1, mapOf(AU.U0 to a))
        val u2a = SNodeBind(u2, mapOf(AU.U0 to a))
        val v1b = SNodeBind(v1, mapOf(AU.U0 to b))
        val v2b = SNodeBind(v2, mapOf(AU.U0 to b))
        val w1c = SNodeBind(w1, mapOf(AU.U0 to c))
        val w2c = SNodeBind(w2, mapOf(AU.U0 to c))

        val list = listOf(Aab, Bbc, u1a, u2a, v1b, v2b, w1c, w2c, z1, z2)
        val r = SPlanEnumerate3().multOrderBySparsity(list)
        println(Explain.explainSPlan(listOf(r), true))
    }


}
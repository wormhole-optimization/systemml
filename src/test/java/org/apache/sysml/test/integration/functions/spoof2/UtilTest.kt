package org.apache.sysml.test.integration.functions.spoof2

import org.apache.sysml.hops.spoof2.enu2.NaturalSubsetStream
import org.apache.sysml.hops.spoof2.enu2.PrefixRejectStream
import org.apache.sysml.hops.spoof2.enu2.PrefixRejectStream.PrefixRejectZone
import org.apache.sysml.hops.spoof2.enu2.noDups
import org.junit.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertTrue

class UtilTest {

    @Test
    fun testNaturalSubsetStream() {
        for (m in 0..6) {
            for (n in 0..m) {
                val s = NaturalSubsetStream(m, n)
                val l = s.drainCopiesTo()
                assertEquals(countComb(m, n), l.size, "m=$m, n=$n")
                assertTrue(l.noDups())
                s.reset()
                assertNotNull(s.top())
//                if (m == 4 && n == 2) {
//                    println(l.joinToString { it.contentToString() })
//                }
            }
        }
    }

    private fun countComb(n: Int, k: Int): Int {
        var r = 1
        for (i in n-k+1..n) r *= i
        for (i in 2..k) r /= i
        return r
    }

    @Test
    fun testPrefixRejectStream() {
        for (m in 2..7) {
            for (n in 0..m) {
                for (nrz in 1..n/2) {
                    for (rzs in genRzs(m, nrz)) {
                        val s = PrefixRejectStream(m,n, rzs)
                        val l = s.drainCopiesTo()
//                        if (m == 5) {
//                            println("n=$n | ["+l.joinToString(",") { it.contentToString() } + "]| Reject "+rzs)
//                        }
                        assertTrue(l.size <= countComb(m, n), "m=$m, n=$n, rzs=$rzs")
                        for (rz in rzs) {
                            l.forEach { a ->
                                val last = (rz.start+1 until rz.start+rz.size).findLast { it in a } ?: return@forEach
                                assertTrue((rz.start until last).all { it in a }, "m=$m, n=$n, l=[${l.joinToString(",") { it.contentToString() }}], offending rz is $rz")
                            }
                        }
                        assertTrue(l.noDups())
                        s.reset()
                        assertNotNull(s.top())
                    }
                }

            }
        }
    }

    private fun genRzs(m: Int, nrz: Int): Iterator<List<PrefixRejectZone>> {
//        if (nrz == 1) return PRZIter(m)
        return ChainPRZIter(m, nrz)
    }

    /**
     * Iterates [PrefixRejectZone]s in [PrefixRejectZone.limit]-monotone order.
     * Start from limit [lower] and continue to limit [m] (inclusive).
     */
    class PRZIter(val m: Int, private val lower: Int = 0) : Iterator<PrefixRejectZone> {
        private var start: Int = lower
        private var limit = lower+2
        override fun hasNext() = limit <= m
        override fun next(): PrefixRejectZone {
            val r = PrefixRejectZone(start,limit-start)
            start++
            if (start > limit-2) {
                limit++
                start = lower
            }
            return r
        }
    }

    /**
     * Iterate over a chain of disjoint [PRZIter] for [m] items.
     */
    class ChainPRZIter(val m: Int, val nrz: Int): AbstractIterator<List<PrefixRejectZone>>() {
        init { require(nrz <= m/2) {"too many nrz $nrz for $m items"} }
        private val iters = (0 until nrz).map { PRZIter(m-(nrz-it-1)*2, it*2) }.toMutableList()
        private val przs = iters.map { it.next() }.toMutableList()
        init { setNext(przs) }
        override fun computeNext() {
            var i = nrz-1
            while (i >= 0 && !iters[i].hasNext()) i--
            if (i == -1) return done()
            przs[i] = iters[i].next()
            for (j in i+1 until nrz) {
                iters[j] = PRZIter(m-(nrz-j-1)*2, przs[j-1].limit)
                przs[j] = iters[j].next()
            }
            return setNext(przs)
        }
    }

}
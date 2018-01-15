package org.apache.sysml.hops.spoof2.enu2

import org.apache.sysml.hops.spoof2.enu2.PrefixRejectTopIter.PrefixRejectZone
import java.util.*

interface TopIterator<out T:Any> {
    fun reset()
    fun next(): T?
    fun top(): T?
}

inline fun <T:Any,R> TopIterator<T>.map(f: (T) -> R): List<R> {
    var t = top()
    val r = mutableListOf<R>()
    while (t != null) {
        r += f(t)
        t = next()
    }
    return r
}

/**
 * Iterates over subsets of size [n] of the natural numbers `0..[m]-1` (these represent [m] data points).
 *
 * Returns **the same array** on each iteration. Copy out the results of the array if you need to resuse them past calls to next.
 * Do NOT change the contents of the array.
 */
open class NaturalSubsetTopIter(val m: Int, val n: Int): TopIterator<IntArray> {
    init { require(m >= n) {"cannot take subsets of size $n from $m points"} }

    protected val p = IntArray(n)
    // stop condition: p[0] == m-n
    protected var finish = false
    init { reset() }

//    fun hasTop(): Boolean = !finish

    override fun reset() {
        for (i in p.indices) p[i] = i
        finish = false // last = m == n
    }

    override fun next(): IntArray? {
//        if (finish) return null //throw NoSuchElementException("finished iterating subsets of size $n from $m points")
        if (finish || isLast()) { finish = true; return null }
        var i = n-1
        while (p[i] == m-n+i) i--
        // i is at a position we can increment
        p[i]++
        for (j in i+1 until n) p[j] = p[i] + j-i
        // stop condition on last one:
//        if (i == 0 && p[0] == m-n) last = true
        return p
    }

    private fun isLast() = n == 0 || p[0] == m-n //p.withIndex().all { (i,pv) -> pv == m-n+i }

    override fun top(): IntArray? = if (finish) null else p

    /** Put all subsets as separate [IntArray]s in a list. */
    fun drainCopiesTo(): List<IntArray> = drainCopiesTo(mutableListOf())
    /** Put all subsets as separate [IntArray]s in [drain]. */
    fun drainCopiesTo(drain: MutableList<IntArray>): MutableList<IntArray> {
        while (!finish) {
            drain += Arrays.copyOf(top(), n)
            next()
        }
        return drain
    }
}

/**
 * A [NaturalSubsetTopIter] that rejects subsets which overlap with one of the [przs] in a non-prefix way.
 * For example, if a rejectZone starts at item 2 and has size 3, then `00110` is accepted while `00101` and `00010` is rejected.
 * Used to prevent enumerating identical items more than once in the same way.
 */
class PrefixRejectTopIter(m: Int, n: Int,
                          rejectZones: List<PrefixRejectZone>
): NaturalSubsetTopIter(m,n) {
    data class PrefixRejectZone(val start: Int, val size: Int): Comparable<PrefixRejectZone> {
        init { require(start >= 0 && size >= 2) {"improper reject zone of size $size (and start $start)"} }
        override fun compareTo(other: PrefixRejectZone): Int {
            val c = start.compareTo(other.start)
            return if (c != 0) c
            else size.compareTo(other.size)
        }
        val limit: Int = start+size
        operator fun contains(i: Int) = i in start until limit
        companion object {
            fun <T> orderGenPrz(edgesSameBase: List<T>): Pair<List<T>, List<PrefixRejectZone>> {
                val g1 = edgesSameBase.groupBy { it }.flatMap {
                    it.value.mapIndexed { i, e -> e to i}
                }
                val prz1: MutableList<PrefixRejectZone> = mutableListOf()
                g1.foldIndexed(null as PrefixRejectZone?) { i, prz, (_,c) ->
                    when {
                        c != 0 -> PrefixRejectZone(i-c, c+1)
                        prz == null -> null
                        else -> { prz1.add(prz); null }
                    }
                }.let { if (it != null) prz1.add(it) }
                return g1.map{it.first} to prz1
            }
        }
    }
    private var first = true
    val przs = rejectZones.sorted()
    init {
        require(rejectZones.all { it.start+it.size <= m }) {"rejectZones out of range: m=$m, n=$n, rzs=$rejectZones"}
        for (i in 0 until rejectZones.size-1)
            require(rejectZones[i].start+rejectZones[i].size <= rejectZones[i+1].start+rejectZones[i+1].size)
            {"overlapping rejectZones $i and ${i+1}: $rejectZones"}
    }

    override fun reset() {
        super.reset()
        first = true
    }

    /** The current subset. Null if the iteration finished. */
    override fun top(): IntArray? {
        if (first) {
            checkReject()
            first = false
        }
        return super.top()
    }

    /** Advance to the next subset. Null if iteration finished. */
    override fun next(): IntArray? {
        super.next()
        checkReject()
        return super.top()
    }

    /** Check if the current subset is acceptable. If not, keep advancing until we find one or iteration finishes. */
    private fun checkReject() {
        loop@while (true) {
            if (finish) return
            var searchStart = 0
            for (rz in przs) {
                // index of rz.start, or `-insertion_point - 1`;
                // insertion point is index of first element greater than rz.start, or p.length if all p's elements less
                var idx = Arrays.binarySearch(p, searchStart, n, rz.start)
                if (idx == -n-1) break@loop
                var seq = idx >= 0 // if true, p[idx] == rz.start
                if (!seq) idx = -(idx + 1)
                while (seq && idx < n - 1 && p[idx] < rz.limit - 2) {
                    idx++; searchStart++
                    if (p[idx] >= rz.limit) break
                    seq = p[idx] == p[idx - 1] + 1
                }
                if (!seq && p[idx] < rz.limit) {
                    reject(idx, rz.limit)
                    continue@loop
                }
            }
            break
        }
    }

    /** Advance pointer [i0] to [rto]. */
    private fun reject(i0: Int, rto: Int) {
        var i = i0
        // i is the pointer number, rto is what it should be set to
        if (rto > m-n+i) {
            if (i == 0) { finish = true; return }
            do i-- while (p[i] == m-n+i)
            p[i]++
        }
        else p[i] = rto
        for (j in i+1 until n) p[j] = p[i] + j-i
        // stop condition on last one:
//        if (i == 0 && p[0] == m-n) finish = true
    }
}

open class PairTopIterator<out T:Any>(private val iter1: TopIterator<T>, private val iter2: TopIterator<T>): TopIterator<Pair<T,T>> {
    override fun reset() {
        iter1.reset(); iter2.reset()
    }

    override fun next(): Pair<T, T>? {
        val v1 = iter1.top() ?: return null
        val v2 = iter2.next()
        if (v2 != null) return v1 to v2
        return nextFirstIter()
    }

    override fun top(): Pair<T, T>? {
        val v1 = iter1.top() ?: return null
        val v2 = iter2.top() ?: return null
        return v1 to v2
    }

    fun nextFirstIter(): Pair<T,T>? {
        val v1 = iter1.next() ?: return null
        iter2.reset()
        return v1 to (iter2.top() ?: return null)
    }
}

class PairPrefixRejectTopIter(
        val n: Int, val m1: Int, val m2: Int,
        val prz1: List<PrefixRejectZone>, val prz2: List<PrefixRejectZone>
): PairTopIterator<IntArray>(PrefixRejectTopIter(m1, n, prz1), PrefixRejectTopIter(m2, n, prz2))
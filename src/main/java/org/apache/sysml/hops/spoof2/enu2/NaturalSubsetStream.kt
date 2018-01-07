package org.apache.sysml.hops.spoof2.enu2

import java.util.*

/**
 * Iterates over subsets of size [n] of the natural numbers `0..[m]-1` (these represent [m] data points).
 *
 * Returns **the same array** on each iteration. Copy out the results of the array if you need to resuse them past calls to next.
 * Do NOT change the contents of the array.
 */
open class NaturalSubsetStream(val m: Int, val n: Int) {
    init { require(m >= n) {"cannot take subsets of size $n from $m points"} }

    protected val p = IntArray(n)
    // stop condition: p[0] == m-n
    protected var finish = false
    init { reset() }

//    fun hasTop(): Boolean = !finish

    open fun reset() {
        for (i in p.indices) p[i] = i
        finish = false // last = m == n
    }

    open fun next(): IntArray? {
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

    open fun top(): IntArray? = if (finish) null else p

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
 * A [NaturalSubsetStream] that rejects subsets which overlap with one of the [rejectZones] in a non-prefix way.
 * For example, if a rejectZone starts at item 2 and has size 3, then `00110` is accepted while `00101` and `00010` is rejected.
 * Used to prevent enumerating identical items more than once in the same way.
 */
class PrefixRejectStream(m: Int, n: Int,
                         rejectZones: List<PrefixRejectZone>
): NaturalSubsetStream(m,n) {
    data class PrefixRejectZone(val start: Int, val size: Int): Comparable<PrefixRejectZone> {
        init { require(start >= 0 && size >= 2) {"improper reject zone of size $size (and start $start)"} }
        override fun compareTo(other: PrefixRejectZone): Int {
            val c = start.compareTo(other.start)
            return if (c != 0) c
            else size.compareTo(other.size)
        }
        val limit: Int = start+size
    }
    private var first = true
    val rejectZones = rejectZones.sorted()
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
            for (rz in rejectZones) {
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
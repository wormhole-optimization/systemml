package org.apache.sysml.hops.spoof2.plan

import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.HopsException
import org.apache.sysml.parser.Expression

// See [Schema].
typealias Attribute = Pair<Name, Shape>
typealias Name = String
typealias Shape = Long
fun Name.isBound() = this.length >= 2

/**
 * Modify the elements of a List in place.
 * @return whether any element was modified.
 */
inline fun <T> MutableList<T>.mapInPlace(f: (T) -> T): Boolean {
    var changed = false
    for (i in this.indices) {
        val o = this[i]
        val n = f(o)
        if (n !== o) {
            changed = true
            this[i] = n
        }
    }
    return changed
}

/**
 * Modify the elements of a List in place.
 * Includes list indices.
 * @return whether any element was modified.
 */
inline fun <T> MutableList<T>.mapInPlaceIndexed(f: (Int, T) -> T): Boolean {
    var changed = false
    for (i in this.indices) {
        val o = this[i]
        val n = f(i, o)
        if (n !== o) {
            changed = true
            this[i] = n
        }
    }
    return changed
}

/**
 * Modify the values of a Map in place.
 * @return whether any element was modified.
 */
inline fun <K,V> MutableMap<K,V>.mapValuesInPlace(f: (V) -> V): Boolean {
    var changed = false
    val keys = this.keys
    for (k in keys) {
        val o = this[k]!!
        val n = f(o)
        if (n !== o) {
            changed = true
            this[k] = n
        }
    }
    return changed
}

/**
 * Modify the keys and values of a Map in place.
 * Copies the map in order to avoid overlap between new and old keys.
 * @return whether any element was modified.
 */
inline fun <K,V> MutableMap<K,V>.mapInPlace(f: (K,V) -> Pair<K,V>): Boolean {
    var changed = false
    val map2 = HashMap(this)
    this.clear()
    map2.forEach { (k,v) ->
        val (kn,vn) = f(k,v)
        if (k !== kn || v !== vn) {
            changed = true
        }
        this[kn] = vn
    }
    return changed
}

inline fun <T,C:Comparable<C>> largerSmaller(i0: T, i1: T, by: (T) -> C): Triple<T,T,IntArray> {
    val c0 = by(i0)
    val c1 = by(i1)
    return if (c0 >= c1)
        Triple(i0 , i1, intArrayOf(0, 1))
    else
        Triple(i1 , i0, intArrayOf(1, 0))
}

fun Hop.isVector(): Boolean = this.dim1 == 1L || this.dim2 == 1L
fun Hop.isRowVector(): Boolean = this.dim1 == 1L

enum class HopClass(val isVector: Boolean) {
    SCALAR(false), ROW_VECTOR(true), COL_VECTOR(true), MATRIX(false);
}
fun Hop.classify(): HopClass {
    HopsException.check(this.dimsKnown(), this, "dims not known: [$dim1, $dim2]")
    if( this.dataType == Expression.DataType.SCALAR )
        return HopClass.SCALAR
    return if (this.dim1 == 1L) {
        if( this.dim2 == 1L )
            HopClass.SCALAR
        else
            HopClass.ROW_VECTOR
    }
    else {
        if( this.dim2 == 1L )
            HopClass.COL_VECTOR
        else
            HopClass.MATRIX
    }
}

fun <T> MutableList<T>.swap(i0: Int, i1: Int) {
    this[i0].let { this[i0] = this[i1]; this[i1] = it }
}


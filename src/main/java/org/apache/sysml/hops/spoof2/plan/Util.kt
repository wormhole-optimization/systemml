package org.apache.sysml.hops.spoof2.plan

import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.HopsException
import org.apache.sysml.hops.spoof2.enu.SumProduct
import org.apache.sysml.parser.Expression

// See [Schema].
//typealias Attribute = Pair<Name, Shape>
typealias Name = Attribute
typealias AB = Attribute.Bound
typealias AU = Attribute.Unbound
typealias Shape = Long
typealias Dim = Int
typealias Id = Long
typealias Hash = String
typealias SPB = SumProduct.Block
typealias ESP = SumProduct.EBlock
typealias SP = SumProduct
typealias SPI = SumProduct.Input
typealias Nnz = Long

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
 * @return whether any element was removed.
 */
inline fun <T> MutableIterable<T>.filterInPlace(f: (T) -> Boolean): Boolean {
    var changed = false
    val iter = this.iterator()
    while (iter.hasNext()) {
        val o = iter.next()
        if( !f(o) ) {
            changed = true
            iter.remove()
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

fun <K,V> Map<K,V>.intersectEntries(m: Map<K,V>): Map<K,V> {
    return this.filter { (k,v) -> m[k] == v }
}

fun <K,V> Map<K,V>.invert(): Map<V,K> {
    return this.map { (k,v) -> v to k }.toMap()
}

fun <T> Iterable<T>.firstSecond(): Pair<T,T> {
    val iterator = iterator()
    if (!iterator.hasNext())
        throw NoSuchElementException("Collection is empty.")
    val f = iterator.next()
    if (!iterator.hasNext())
        throw NoSuchElementException("Collection has one element.")
    return f to iterator.next()
}

inline fun <T> Iterable<T>.sumByLong(selector: (T) -> Long): Long {
    var sum = 0L
    for (element in this) {
        sum += selector(element)
    }
    return sum
}

fun <T> Iterable<T>.disjoint(b: Iterable<T>): Boolean {
    return this.all { it !in b }
}

/** "Agnostic bindings", for SNodeBind or SNodeUnbind. */
fun SNode.agBindings(): MutableMap<AU, AB> = when(this) {
    is SNodeBind -> this.bindings
    is SNodeUnbind -> this.unbindings
    else -> throw IllegalArgumentException()
}

/**
 * Dead code elimination.
 * If the node does not have parents, then eliminate it and remove it from the parents of all inputs.
 * Repeat recursively.
 *
 * @param noStrip do not strip the inputs of these nodes (forced dead code elim stop points)
 */
fun stripDead(node: SNode, noStrip: Set<SNode> = setOf()) {
    if( node.parents.isEmpty() && node.inputs.isNotEmpty() && node !in noStrip )
        rStripDead(mutableSetOf(node), noStrip)
}
private tailrec fun rStripDead(toRemove: MutableSet<SNode>, noStrip: Set<SNode>) {
    if( toRemove.isEmpty() )
        return
    val node = toRemove.first()
    toRemove -= node
    toRemove += node.inputs.toSet().filter {
        it.parents.removeIf { it == node }
        it.parents.isEmpty() && it.inputs.isNotEmpty() && it !in noStrip
    }
    return rStripDead(toRemove, noStrip)
}

/**
 * Undo dead code elimination.
 * Used to resurrect nodes that were thrown away during plan enumeration
 * but still cached in case they are explored again.
 */
fun unstripDead(node: SNode) {
    node.inputs.filter { node !in it.parents }.forEach {
        it.parents += node
        unstripDead(it)
    }
}

fun Iterable<Long>.prod(): Long {
    var accumulator = 1L
    for (element in this) accumulator *= element
    return accumulator
}
fun Iterable<Double>.prod(): Double {
    var accumulator = 1.0
    for (element in this) accumulator *= element
    return accumulator
}

fun Collection<Schema>.unionSchema(): Schema = this.fold(Schema()) { acc, schema ->
    acc += schema; acc
}

fun <K,V1,V2> Map<K,V1>.zipIntersect(m: Map<K,V2>): Map<K, Pair<V1,V2>> {
    val list: List<Map.Entry<K, Pair<Boolean, Any?>>> = this.mapValues { (_,v) -> false to v }.entries.toList() + m.mapValues { (_,v) -> true to v }.entries
    return list.groupBy { it.key }.filterValues { it.size == 2 }.mapValues { (_,vo) ->
        val v = vo.map { it.value }
        val (v2,v1) = v.partition { it.first }
        assert(v2.size == 1 && v1.size == 1)
        @Suppress("UNCHECKED_CAST")
        v1[0].second as V1 to v2[0].second as V2
    }
}

fun <T> List<T>.permute(newIndices: List<Int>): List<T> {
    return newIndices.map(this::get)
}

fun <E> List<List<E>>.cartesian(): Sequence<List<E>> {
    return object : Sequence<List<E>> {
        override fun iterator(): Iterator<List<E>> = CartesianIterator(this@cartesian)
    }
}

private class CartesianIterator<out E>(
        private val lists: List<List<E>>
): Iterator<List<E>> {
    private val ptrs = IntArray(lists.size)
    private var nextValid = lists.all { it.isNotEmpty() }

    fun reset() {
        nextValid = lists.all { it.isNotEmpty() }
        ptrs.fill(0)
    }

    override fun hasNext(): Boolean {
        return nextValid
    }

    override fun next(): List<E> {
        val result = lists.mapIndexed { i, list -> list[ptrs[i]] }
        var i = lists.size-1
        while( i >= 0 && ptrs[i] == lists[i].size - 1 ) {
            ptrs[i] = 0
            i--
        }
        if( i == -1 )
            nextValid = false
        else
            ptrs[i]++
        return result
    }

}

fun <E> MutableCollection<E>.removeFirst(): E? {
    return if( this.isEmpty() ) null
    else this.first().also { this.remove(it) }
}


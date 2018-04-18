package org.apache.sysml.hops.spoof2.plan

import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.HopsException
import org.apache.sysml.hops.spoof2.enu.SumProduct
import org.apache.sysml.parser.Expression
import java.util.*

// See [Schema].
//typealias Attribute = Pair<Name, Shape>
typealias Name = Attribute
typealias AB = Attribute.Bound
typealias AU = Attribute.Unbound
typealias Shape = Long
typealias Dim = Int
typealias Id = Long
typealias Rep = String
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

fun BooleanArray.disjoint(b: BooleanArray): Boolean {
    return this.indices.none { this[it] && b[it] }
}

fun BooleanArray.or(b: BooleanArray): BooleanArray {
    require(size == b.size)
    return BooleanArray(size) { i -> this[i] || b[i] }
}

/** Is evey true position in this also true in either [a] or [b]? */
fun BooleanArray.coveredBy(a: BooleanArray, b: BooleanArray): Boolean {
    require(size == a.size && size == b.size)
    for (i in indices)
        if (this[i] && !a[i] && !b[i])
            return false
    return true
}

fun other01(n: Int): Int = when (n) {
    0 -> 1
    1 -> 0
    else -> throw AssertionError()
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

fun <E> MutableCollection<E>.removeLast(): E? {
    return if( this.isEmpty() ) null
    else this.last().also { this.remove(it) }
}

fun <A:Comparable<A>,B:Comparable<B>> pairComparator(): Comparator<Pair<A,B>> {
    return Comparator.comparing<Pair<A,B>,A> { it.first }.thenBy {it.second}
}

fun <A:Comparable<A>> listComparator(): Comparator<List<A>> = ListComparator<A>()

private class ListComparator<C:Comparable<C>>: Comparator<List<C>> {
    override fun compare(o1: List<C>, o2: List<C>): Int {
        val i1 = o1.iterator()
        val i2 = o2.iterator()
        while (i1.hasNext() && i2.hasNext()) {
            val c = i1.next().compareTo(i2.next())
            if (c != 0) return c
        }
        return i1.hasNext().compareTo(i2.hasNext())
    }

}

fun <V> findCCs(edges: Map<V, Set<V>>, verts: Set<V>): Set<Set<V>> {
    val ret = mutableSetOf<Set<V>>()
    val vertsRemain = verts.toMutableSet()
    while (vertsRemain.isNotEmpty()) {
        val a = vertsRemain.first()
        val component = findCC(verts, a, edges)
        vertsRemain -= component
        ret += component
    }
    return ret
}

private fun <V> findCC(verts: Set<V>, v: V, edges: Map<V, Set<V>>): Set<V> {
    var toExplore = setOf(v)
    val explored = mutableSetOf<V>()
    do {
        val found = toExplore.flatMap { edges[it] ?: setOf() }.toSet()
        explored += toExplore
        toExplore = found - explored
    } while (toExplore.isNotEmpty())
    return explored
}

fun Collection<Int>.toDenseArray(sz: Int): IntArray = IntArray(sz) { i -> this.count { i == it } }

//fun <T> List<List<T>>.groupInnerWithOuterIndex(): Map<T, List<Int>> =
//        this.withIndex().flatMap { (i, x) -> x.map { IndexedValue(i, it) } }
//                .groupBy { it.value }
//                .mapValues { (k, iv) -> iv.map { it.index } }
//
//fun <T> List<List<T>>.groupInnerWithOuterIndexDense(): Map<T, IntArray> =
//        this.withIndex().flatMap { (i, x) -> x.map { IndexedValue(i, it) } }
//                .groupBy { it.value }
//                .mapValues { (_, iv) -> iv.map { it.index }.toDenseArray(this.size) }


fun <T> List<List<T>>.groupInnerWithOuterIndexDense(): Pair<List<T>, List<IntArray>> {
    val uniques = this.flatten().distinct()
    val incl = this.map { l ->
        IntArray(uniques.size) { i -> l.count { it == uniques[i] } }
    }
    return uniques to incl
}



inline fun <T> Iterable<T>.partitionIndexed(predicate: (IndexedValue<T>) -> Boolean): Pair<List<T>, List<T>> {
    val first = ArrayList<T>()
    val second = ArrayList<T>()
    for (element in this.withIndex()) {
        if (predicate(element)) {
            first.add(element.value)
        } else {
            second.add(element.value)
        }
    }
    return Pair(first, second)
}

inline fun <A,R> Pair<A,A>.map(f: (A) -> R): Pair<R,R> = f(this.first) to f(this.second)

fun makeRenameAbove(n: SNode, map: Map<AB, AB>): SNode {
    if (map.all { (k,v) -> k == v })
        return n
    val (unbindMap, bindMap) = map.entries.mapIndexed { i, (k,v) ->
        AU(i).let { (it to k) to (it to v) }
    }.unzip()
    return makeBindAbove(makeUnbindAbove(n, unbindMap.toMap()), bindMap.toMap())
}

fun makeBindAbove(n: SNode, tgtMap: Map<AU, AB>): SNode {
    return if (tgtMap.isEmpty()) n
    else n.parents.find { it is SNodeBind && it.bindings == tgtMap } ?: SNodeBind(n, tgtMap)
}
fun makeUnbindAbove(n: SNode, tgtMap: Map<AU, AB>): SNode {
    return if (tgtMap.isEmpty()) n
    else n.parents.find { it is SNodeUnbind && it.unbindings == tgtMap } ?: SNodeUnbind(n, tgtMap)
}
fun makeMultAbove(vararg ns: SNode): SNodeNary {
    //    Spoof2Compiler.LOG.trace("make *: (${m.id}) ${m.schema} -- [${ns.joinToString { "${it.id} $it ${it.schema}" }}]")
    return makeMultAbove(ns.asList())
}
fun makeMultAbove(ns: Collection<SNode>) = makeNaryAbove(ns, SNodeNary.NaryOp.MULT)
fun makePlusAbove(vararg ns: SNode) = makePlusAbove(ns.asList())
fun makePlusAbove(ns: Collection<SNode>) = makeNaryAbove(ns, SNodeNary.NaryOp.PLUS)
private fun makeNaryAbove(ns: Collection<SNode>, op: SNodeNary.NaryOp): SNodeNary {
    require(ns.isNotEmpty())
    val nsl = ns.toList().sortedBy { it.id }
    return ns.first().parents.find { it is SNodeNary && it.op == op && it.inputs.sortedBy { it.id } == nsl } as SNodeNary? ?: SNodeNary(op, nsl)
}
fun makeAggAbove(n: SNode, aggs: Set<AB>): SNodeAggregate {
    // todo do I need this?
//    if (n is SNodeAggregate && n.op == Hop.AggOp.SUM) {
//        @Suppress("UNCHECKED_CAST")
//        val allAggs = aggs + n.aggs.names as Set<AB>
//        return n.input.parents.find { it is SNodeAggregate && it.op == Hop.AggOp.SUM && it.aggs.keys == allAggs } as SNodeAggregate?
//                ?: SNodeAggregate(Hop.AggOp.SUM, n.input, allAggs)
//    }
    return n.parents.find { it is SNodeAggregate && it.op == Hop.AggOp.SUM && it.aggs.keys == aggs } as SNodeAggregate?
            ?: SNodeAggregate(Hop.AggOp.SUM, n, aggs)
}
fun makeAggAbove(n: SNode, vararg aggs: AB): SNodeAggregate {
    return makeAggAbove(n, aggs.toSet())
}

/**
 * Return all roots (0-parent nodes) that are ancestors of [n].
 * Stops at nodes already in the [memo]; adds visited nodes to [memo].
 */
fun getRootsAbove(n: SNode, memo: MutableSet<SNode> = mutableSetOf()): Set<SNode> {
    return mutableSetOf<SNode>().also { getRootsAbove(n, memo, it) }
}
fun getRootsAbove(n: SNode, memo: MutableSet<SNode>, roots: MutableSet<SNode>) {
    if (n in memo) return
    memo += n
    if (n.parents.isEmpty()) roots += n
    else n.parents.forEach { getRootsAbove(it, memo, roots) }
}

fun <T> List<T>.bagMinus(subAll: List<T>): List<T> {
    return subAll.fold(this) { acc, sub ->
        acc - sub
    }
}

class EnumerateIndices(limitsExcl: IntArray): Iterator<IntArray> {
    private val limitsIncl = IntArray(limitsExcl.size) { limitsExcl[it] - 1 }
    val ret = IntArray(limitsIncl.size)
    init {
        require(limitsIncl.all { it >= 0 })
    }
    private var done = false
    private var first = true

    override fun hasNext(): Boolean {
        return !done
    }

    override fun next(): IntArray {
        if (first) {
            first = false
            done = limitsIncl.isNotEmpty()
            return ret
        }
        increment()
        return ret
    }

    private fun increment() {
        var i = ret.size-1
        while (i >= 0 && ret[i] == limitsIncl[i]) {
            ret[i] = 0
            i--
        }
        if (i >= 0)
            ret[i]++
        done = i < 0 || ret[i] == limitsIncl[i] && ret.indices.all { j -> ret[j] == limitsIncl[j] }
    }
}

fun Boolean.toCharStr() = if (this) "T" else "F"
fun BooleanArray.toDenseString(): String = joinToString("", transform = Boolean::toCharStr)

inline fun extractHops(roots: List<Hop>, condition: (Hop) -> Boolean): Set<Hop> {
    Hop.resetVisitStatus(roots)
    val found: MutableSet<Hop> = mutableSetOf()
    val frontier: NavigableSet<Hop> = java.util.TreeSet(compareBy { it.input.size })
    frontier += roots

    while (frontier.isNotEmpty()) {
        val node = frontier.pollFirst()
        node.setVisited()
        if (condition(node)) found += node
        node.input.filterTo(frontier) { !it.isVisited }
    }

    Hop.resetVisitStatus(roots)
    return found
}

inline fun <T> fixedListOf(size: Int, initial: () -> T): List<T> {
    val l = mutableListOf<T>()
    repeat(size) { l.add(initial()) }
    return l.toList()
}

inline fun <T> Iterable<T>.findIndexed(predicate: (Int, T) -> Boolean): T? {
    for ((i, element) in this.withIndex()) if (predicate(i, element)) return element
    return null
}


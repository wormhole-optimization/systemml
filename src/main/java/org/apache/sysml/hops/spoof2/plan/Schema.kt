package org.apache.sysml.hops.spoof2.plan

import java.util.*

/**
 * An Attribute consists of a Name and a Shape.
 * Bound attributes have a Name with at least two characters.
 * Unbound attributes have a Name with 0 or 1 characters.
 * Only LeftIndex and RightIndex operators are allowed to have schemas with unbound attributes.
 */
class Schema private constructor(
        private val nameShapes: HashMap<Name,Shape>
): MutableMap<Name, Shape> by nameShapes {
    // defensive copy constructors
    constructor() : this(hashMapOf())
    constructor(names: List<Name>, shapes: List<Shape>) : this(names.zip(shapes).toMap(HashMap<Name,Shape>())) {
        require(names.size == shapes.size) {"different number of names and shapes: $names, $shapes"}
    }
    constructor(s: Schema) : this(HashMap<Name,Shape>(s.nameShapes))
    constructor(m: Collection<Pair<Name,Shape>>) : this(m.toMap(HashMap<Name,Shape>()))
    constructor(m: Map<Name,Shape>) : this(m.toMap(HashMap<Name,Shape>()))

    val names: Set<Name>
        get() = nameShapes.keys
    val shapes: Collection<Shape>
        get() = nameShapes.values

//    operator fun contains(name: Name) = name in names
    operator fun plusAssign(other: Schema) {
        putAll(other)
    }

    override fun toString(): String {
        return nameShapes.map { (n,s) -> "$n-$s" }.joinToString(prefix = "{", postfix = "}")
    }

    fun setTo(s: Schema) {
        clear()
        nameShapes += s.nameShapes
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other?.javaClass != javaClass) return false

        other as Schema

        if (nameShapes != other.nameShapes) return false

        return true
    }
    override fun hashCode() = nameShapes.hashCode()

    fun allBound() = names.all { it is Attribute.Bound }

    fun unbindName(name: Attribute.Bound, dim: Dim) {
        val shape = nameShapes.remove(name) ?: throw IllegalArgumentException("attempt to unbind a name $name that is not in the schema $this")
        nameShapes.put(name.unbind(dim), shape)
    }

    /**
     * Create names to bind all the unbound attributes in this Schema.
     * Add them to [partialBindings].
     * Retain any bindings already in [partialBindings].
     */
    fun fillWithBindings(partialBindings: MutableMap<AU, AB>) {
        this.names.forEach {
            if( it is AU && it !in partialBindings )
                partialBindings.put(it, it.bindFresh())
        }
    }
    fun genAllBindings(): MutableMap<AU, AB> = linkedMapOf<AU,AB>().also { this.fillWithBindings(it) }


    companion object {
        fun copyShapes(src: Schema, tgt: Iterable<Name>): Schema {
            val s = Schema()
            tgt.forEach { n ->
                check( n in src ) {"error copying schema information from $src to names $tgt; src does not contain name $n"}
                s.put(n, src[n]!!)
            }
            return s
        }
        fun copyShapes(src: Schema, vararg names: Name): Schema {
            return copyShapes(src, names.asList())
        }
    }

    
    inline fun filterKeys(predicate: (Attribute) -> Boolean): Schema {
        return filterKeysTo(Schema(), predicate)
    }
    inline fun filterKeysTo(destination: Schema, predicate: (Attribute) -> Boolean): Schema {
        val result = destination
        for ((key, value) in this)
            if (predicate(key))
                result.put(key, value)
        return result
    }
    inline fun filter(predicate: (Attribute, Shape) -> Boolean): Schema {
        return filterTo(Schema(), predicate)
    }
    inline fun filterTo(destination: Schema, predicate: (Attribute, Shape) -> Boolean): Schema {
        val result = destination
        for ((key, value) in this)
            if (predicate(key, value))
                result.put(key, value)
        return result
    }
    fun filterBound() = filter { a, _ -> a is Attribute.Bound }
    operator fun minusAssign(other: Schema) {
        other.forEach { remove(it.key) }
    }
    fun replaceKey(aOld: Attribute, aNew: Attribute): Boolean {
        val changed = if( aOld != aNew ) {
            val shape = remove(aOld) ?: throw IllegalArgumentException("old attribute $aOld is not present in this schema")
            put(aNew, shape)
            true
        } else false
        return changed
    }
    inline fun replaceKeys(oldToNew: (Attribute) -> Attribute): Boolean {
        val m0 = keys.mapTo(mutableListOf()) { it to oldToNew(it) }
        var changed = false
        do {
            val iter = m0.iterator()
            while( iter.hasNext() ) {
                val (o, n) = iter.next()
                when{
                    o == n -> iter.remove()
                    n in this -> {}
                    else -> {changed = replaceKey(o, n) || changed; iter.remove()}
                }
            }
        } while(m0.isNotEmpty())
        return changed
    }
    inline fun partition(predicate: (Name, Shape) -> Boolean): Pair<Schema, Schema> {
        val first = Schema()
        val second = Schema()
        for ((n,s) in this) {
            if (predicate(n,s)) {
                first.put(n,s)
            } else {
                second.put(n,s)
            }
        }
        return Pair(first, second)
    }


    fun leastFreeUnbound(): AU {
        var au = AU.U0
        while( au in this )
            au = AU(au.dim+1)
        return au
    }
}

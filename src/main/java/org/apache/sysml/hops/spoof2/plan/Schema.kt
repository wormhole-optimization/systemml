package org.apache.sysml.hops.spoof2.plan

import org.apache.sysml.runtime.controlprogram.parfor.util.IDSequence
import java.util.*

/**
 * An Attribute consists of a Name and a Shape.
 * Bound attributes have a Name with at least two characters.
 * Unbound attributes have a Name with 0 or 1 characters.
 * Only LeftIndex and RightIndex operators are allowed to have schemas with unbound attributes.
 */
class Schema private constructor(
        val names: ArrayList<Name>,
        val shapes: ArrayList<Shape>
) {
    constructor() : this(arrayListOf(), arrayListOf())
    constructor(names: List<Name>, shapes: List<Shape>) : this(ArrayList(names), ArrayList(shapes))
    constructor(s: Schema) : this(ArrayList(s.names), ArrayList(s.shapes))

    init { check() }
    fun check() {
        require(names.size == shapes.size) {"mismatched names and shapes in Schema $this"}
    }

    companion object {
        private val _idSeq = IDSequence()
        private fun nextNameId(): String = _idSeq.nextID.toString()
    }

    fun deepCopy() = Schema(this)

    operator fun contains(name: Name) = name in names

    fun getShape(name: Name): Shape {
        val idx = names.indexOf(name)
        require(idx != -1) {"no such name $name in $this"}
        return shapes[idx]
    }

    fun getName(position: Int): Name {
        return names[position]
    }

    fun setTo(s: Schema) {
        clear()
        names += s.names
        shapes += s.shapes
    }

    /** Append the attributes from [s] that are not already in this to this. */
    fun unionWithBound(s: Schema) {
        check( s.allBound() ) {"cannot union with a Schema with unbound attributes; $this; $s"}
        s.names.zip(s.shapes).forEach { (l,d) ->
            if (l !in names) {
                names += l
                shapes += d
            }
        }
    }

    fun clear() {
        names.clear()
        shapes.clear()
    }

    /** Remove the bound attributes that are in [removes]. */
    fun removeBoundAttributes(removes: Iterable<Name>) {
        removes.forEach { l ->
            if( l.isBound() ) {
                val idx = names.indexOf(l)
                if (idx != -1) {
                    names.removeAt(idx)
                    shapes.removeAt(idx)
                }
            }
        }
    }

    override fun toString(): String {
        return "$names:$shapes"
//        names.zip(dims).joinToString(prefix = "[", postfix = "]", transform = { (l,d) -> "$l: $d" })
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other?.javaClass != javaClass) return false

        other as Schema

        if (names != other.names) return false
        if (shapes != other.shapes) return false

        return true
    }

    override fun hashCode() = 31 * names.hashCode() + shapes.hashCode()

    fun allBound() = names.all(Name::isBound)
    fun isBound(pos: Int) = names[pos].isBound()

    /** Add a new unbound attribute */
    fun addUnboundAttribute(shape: Shape, namePrefix: NamePrefix) {
        names += namePrefix.prefixStr
        shapes += shape
    }

    enum class NamePrefix(val prefixChar: Char) {
        ROW('r'), COL('c');
        val prefixStr: String = prefixChar.toString()
    }

    fun unbindName(name: Name) {
        require(name.isBound()) {"attempt to unbind an invalid name $name from schema $this"}
        val idx = names.indexOf(name)
        require(idx != -1) {"attempt to unbind a name $name that is not in the schema $this"}
        names[idx] = name.substring(0, 1)
    }

    fun bindName(pos: Int, name: Name) {
        val pre = names[pos]
        require(!pre.isBound()) {"name $pre at position $pos is already bound in schema $this"}
        names[pos] = name // replace pre
    }

    fun permute(permutation: Map<Name, Name>) {
//        println("permutation: $permutation\nbefore: $names")
        val indexMap = names.mapIndexed { idx, n ->
            if (n in permutation) {
                val newidx = names.indexOf(permutation[n])
                require(newidx != -1) {"bad permutation $permutation on $this"}
                newidx
            } else
                idx
        }
        val tmpNames = ArrayList(names)
        names.mapInPlaceIndexed { idx, _ -> tmpNames[indexMap[idx]] }
        val tmpShapes = ArrayList(shapes)
        shapes.mapInPlaceIndexed { idx, _ -> tmpShapes[indexMap[idx]] }
//        println("after: $names")
    }

    fun isEmpty() = names.isEmpty()
    fun isNotEmpty() = names.isNotEmpty()
    val size: Int
        get() = names.size
    val indices: IntRange
        get() = 0..size - 1

    /**
     * Create names to bind all the unbound attributes in this Schema.
     * Add them to [partialBindings].
     * Retain any bindings already in [partialBindings].
     */
    fun fillWithBindings(partialBindings: MutableMap<Int, Name>) {
        this.indices.map {
            if( it in partialBindings )
                require(!names[it].isBound()) {"required binding to position $it is already bound in $this"}
            else if( !names[it].isBound() )
                partialBindings[it] = names[it] + nextNameId()
        }
    }

    fun genAllBindings(): MutableMap<Int, Name> = hashMapOf<Int,Name>().also { this.fillWithBindings(it) }
}
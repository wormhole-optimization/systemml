package org.apache.sysml.hops.spoof2.plan

import org.apache.sysml.runtime.controlprogram.parfor.util.IDSequence

sealed class Attribute : Comparable<Attribute> {
    fun isBound() = this is Bound

    class Unbound private constructor(
            val dim: Dim
    ): Attribute() {
        companion object {
            private val dimMap: MutableMap<Dim, Unbound> = mutableMapOf()
            fun construct(dim: Dim) = dimMap.computeIfAbsent(dim) { Unbound(dim) }
            operator fun invoke(dim: Dim) = construct(dim)
            val U0 = construct(0)
            val U1 = construct(1)
            val U2 = construct(2)
        }

        fun bindFresh() = Attribute.Bound()

        override fun toString() = "_$dim"
        /*override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (javaClass != other?.javaClass) return false

            other as Unbound

            if (dim != other.dim) return false

            return true
        }
        override fun hashCode(): Int {
            return dim
        }*/
        override fun compareTo(other: Attribute): Int {
            return when( other ) {
                is AU -> this.dim.compareTo(other.dim)
                is AB -> -1
            }
        }
    }


    class Bound private constructor(
            val id: Id,
            val derivedFrom: Attribute?
    ): Attribute() {
        constructor(): this(_idSeq.nextID, null)
        constructor(derivedFrom: Attribute): this(_idSeq.nextID, derivedFrom)

        companion object {
            private val _idSeq = IDSequence()
        }

        fun deriveFresh() = Attribute.Bound(this)
        fun unbind(dim: Dim) = Attribute.Unbound(dim)

        override fun toString(): String {
            return if( derivedFrom == null )
                "$id"
            else
                "${derivedFrom}_$id"
        }
        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (javaClass != other?.javaClass) return false

            other as Attribute.Bound

            if (id != other.id) return false

            return true
        }
        override fun hashCode() = id.hashCode()
        override fun compareTo(other: Attribute): Int {
            return when( other ) {
                is AU -> 1
                is AB -> this.id.compareTo(other.id)
            }
        }
    }
}

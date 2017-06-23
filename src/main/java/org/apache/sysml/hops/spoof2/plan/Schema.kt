package org.apache.sysml.hops.spoof2.plan

import org.apache.sysml.runtime.controlprogram.parfor.util.IDSequence
import java.util.*

/**
 * Properties of an SNode.
 * An SNode has exposed indices `labels`, each with matching dimension in `dims`.
 * The base type of each entry is a tensor with shape `type`. (length 0 is scalar; 1 is vector; etc.)
 */
class Schema {
    val labels: ArrayList<String> = arrayListOf()
    val dims: ArrayList<Long> = arrayListOf()
    val type: ArrayList<Long> = arrayListOf()

    fun setType(vararg typeDims: Long, rowVector: Boolean? = null) {
        type.clear()
        typeDims.toCollection(type)
        if (rowVector != null)
            this.rowVector = rowVector
    }
    fun setType(typeDims: List<Long>, rowVector: Boolean? = null) {
        type.clear()
        typeDims.toCollection(type)
        if (rowVector != null)
            this.rowVector = rowVector
    }

    /** If not a vector, then this doesn't matter. If a vector, gives orientation. */
    var rowVector: Boolean = false

    init { check() }
    fun check() {
        require(labels.size == dims.size) {"mismatched labels and dims in Schema $this"}
    }

    companion object {
        private val _idSeq = IDSequence()
        fun nextLabel(): String = "i" + _idSeq.nextID
    }

    fun deepCopy() = Schema().let { it += this; it.type.addAll(type) }

    operator fun contains(label: String) = label in labels

    operator fun get(label: String): Long {
        val idx = labels.indexOf(label)
        require(idx != -1) {"no such label $label in $this"}
        return dims[idx]
    }

    /** Add the labels and dimensions from [s] that are not already in this to this. */
    operator fun plusAssign(s: Schema) {
        s.labels.zip(s.dims).forEach { (l,d) ->
            if (l !in labels) {
                labels += l
                dims += d
            }
        }
    }

    /** Remove the labels and dimensions from this that are not in [s]. */
    fun retainOnly(s: Schema) {
        s.labels.zip(s.dims).forEach { (l,_) ->
            val idx = labels.indexOf(l)
            if (idx == -1) {
                labels.removeAt(idx)
                dims.removeAt(idx)
            }
        }
    }

    fun clearLabelsTypes() {
        labels.clear()
        dims.clear()
        type.clear()
    }

    override fun toString(): String {
        return "(Schema: ${labels.zip(dims)
                .joinToString(prefix = "[", postfix = "]", transform = { (l,d) -> "$l: $d" })
        }: $type${if (type.size != 1) "" else if (rowVector) "[R]" else "[C]"})"
    }
}
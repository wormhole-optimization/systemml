package org.apache.sysml.hops.spoof2.plan

import org.apache.sysml.hops.HopsException
import java.util.ArrayList

import org.apache.sysml.runtime.controlprogram.parfor.util.IDSequence

abstract class SNode() {

    //globally unique SNode id
    val id: Long = _idSeq.nextID
    val parents: ArrayList<SNode> = ArrayList()
    val inputs: ArrayList<SNode> = ArrayList()
    var visited: Boolean = false

    // exposed indices, labels of exposed indices, type of base object
    val schema = Schema() // initial schema is uncomputed

    /** Set the [schema] as a function of this SNode's type and inputs.
     * Re-compute this after changing the node's inputs. */
    abstract fun updateSchema()

    constructor(vararg inputs: SNode) : this(inputs.asList())
    constructor(inputs: List<SNode>) : this() {
        for (input in inputs) {
            this.inputs.add(input)
            input.parents.add(this)
        }
    }

//    val isScalar: Boolean
//        get() = _dims.isEmpty() || _dims.size == 2 && _dims[0] == 0L && _dims[1] == 0L

//    val numDims: Int
//        get() = _dims.size
//
//    fun getDim(pos: Int): Long {
//        return _dims[pos]
//    }
//
//    fun getDim(attr: String): Long {
//        return _dims[_schema.indexOf(attr)]
//    }

//    val dim1: Long
//        get() = getDim(0)
//
//    val dim2: Long
//        get() = if (numDims >= 2)
//            getDim(1)
//        else
//            1
//
//    fun setDims(vararg dims: Long) {
//        _dims = dims
//    }

    fun resetVisited() {
        if (!visited)
            return
        for (c in inputs)
            c.resetVisited()
        visited = false
    }

    abstract val isSchemaAggregator: Boolean
    abstract val isSchemaPropagator: Boolean
    abstract override fun toString(): String

    /**
     * Check whether this SNode has a correct number of inputs. Some ops only allow a single input (transpose, exp)
     * while others allow any number of inputs (mult).
     *
     * @throws HopsException if this SNode has an illegal number of inputs (a kind of Illegal State)
     */
    @Throws(HopsException::class)
    abstract fun checkArity()

    inline fun check(condition: Boolean, message: () -> String) {
        SNodeException.check(condition, this, message)
    }
    fun checkLabels() {
        // no label can appear more than once in an input
        this.check( schema.labels.size == schema.labels.distinct().size ) {"a label appears more than once in $schema"}
    }

    companion object {
        private val _idSeq = IDSequence()

        @JvmStatic
        fun resetVisited(roots: ArrayList<SNode>) {
            for (root in roots)
                root.resetVisited()
        }
    }
}

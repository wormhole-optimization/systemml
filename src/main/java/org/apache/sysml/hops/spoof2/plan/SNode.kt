package org.apache.sysml.hops.spoof2.plan

import java.util.ArrayList

import org.apache.sysml.runtime.controlprogram.parfor.util.IDSequence

abstract class SNode() {

    //globally unique SNode id
    val id: Long
    //SNode parent nodes
    private val _parents: ArrayList<SNode>
    //SNode child nodes and associated indexes
    private val _inputs: ArrayList<SNode>
    private val _indexes: ArrayList<Indexes>

    //output dimensions and meta data
    @JvmField
    protected val _schema: ArrayList<String>
    protected var _dims: LongArray = longArrayOf()
    var isVisited: Boolean = false

    init {
        id = _idSeq.nextID
        _parents = ArrayList<SNode>()
        _inputs = ArrayList<SNode>()
        _indexes = ArrayList<Indexes>()
        _schema = ArrayList<String>()
    }

    constructor(input: SNode) : this() {
        _inputs.add(input)
        input._parents.add(this)
    }

    constructor(inputs: List<SNode>) : this() {
        for (input in inputs) {
            _inputs.add(input)
            input._parents.add(this)
        }
    }

    val parent: List<SNode>
        get() = _parents

    val input: List<SNode>
        get() = _inputs

    val indexes: List<Indexes>
        get() = _indexes

    var schema: List<String>
        get() = _schema
        set(schema) {
            _schema.clear()
            _schema.addAll(schema)
        }

    val isScalar: Boolean
        get() = _dims.isEmpty() || _dims.size == 2 && _dims[0] == 0L && _dims[1] == 0L

    val numDims: Int
        get() = _dims.size

    fun getDim(pos: Int): Long {
        return _dims[pos]
    }

    fun getDim(attr: String): Long {
        return _dims[_schema.indexOf(attr)]
    }

    val dim1: Long
        get() = getDim(0)

    val dim2: Long
        get() = if (numDims >= 2)
            getDim(1)
        else
            1

    fun setDims(vararg dims: Long) {
        _dims = dims
    }

    fun setVisited() {
        isVisited = true
    }

    fun resetVisited() {
        if (!isVisited)
            return
        for (c in input)
            c.resetVisited()
        isVisited = false
    }

    abstract val isIndexAggregator: Boolean

    abstract val isIndexPropagator: Boolean

    abstract override fun toString(): String

    protected fun setupBasicSchema(hopID: Long) {
        _schema.add("i1_" + hopID)
        _schema.add("i2_" + hopID)
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

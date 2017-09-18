package org.apache.sysml.hops.spoof2.plan

import com.google.common.collect.HashMultiset
import com.google.common.collect.Multiset
import org.apache.sysml.hops.spoof2.plan.SNodeNary.NaryOp.*

class SNodeNary(
        val op: NaryOp,
        inputs: List<SNode>
) : SNode(inputs) {
    init {
        refreshSchema()
    }

    enum class NaryOp(val commutative: Boolean = false) {
        //unary operations
        NOT,
        ABS, SIN, COS, TAN, ASIN, ACOS, ATAN, SIGN, SQRT, LOG, EXP,
        ROUND, CEIL, FLOOR,
        SPROP, SIGMOID, SELP, LOG_NZ,

        //binary operations
        PLUS(true),
        MINUS, MULT(true), DIV, MODULUS, INTDIV,
        LESS, LESSEQUAL, GREATER, GREATEREQUAL, EQUAL(true), NOTEQUAL(true),
        MIN(true), MAX(true), AND(true), OR(true), POW, //LOG (see unary)

        //ternary operations
        PLUS_MULT,
        MINUS_MULT;

        companion object {
            operator fun contains(value: String): Boolean {
                return values().any { it.name == value }
            }
        }
    }

    override fun shallowCopyNoParentsYesInputs() = SNodeNary(op, inputs)
    override fun compare(o: SNode): Boolean {
        if( o !is SNodeNary || o.op != this.op)
            return false
        if( o.inputs == this.inputs )
            return true
        return false
    }

    fun compareCommutative(o: SNode): Boolean {
        if( o !is SNodeNary || o.op != op)
            return false
        // warning: if the schema is different, need to adjust
        return op.commutative && o.inputs.toSet() == this.inputs.toSet()
    }

    constructor(op: NaryOp, vararg inputs: SNode) : this(op, inputs.asList())

    override fun toString(): String {
        return when (op) {
            PLUS ->         "nary(+)"
            MINUS ->        "nary(-)"
            MULT ->         "nary(*)"
            DIV ->          "nary(/)"
            MODULUS ->      "nary(%%)"
            INTDIV ->       "nary(%/%)"
            LESS ->         "nary(<)"
            LESSEQUAL ->    "nary(<=)"
            GREATER ->      "nary(>)"
            GREATEREQUAL -> "nary(>=)"
            EQUAL ->        "nary(==)"
            NOTEQUAL ->     "nary(!=)"
            PLUS_MULT ->    "nary(+*)"
            MINUS_MULT ->   "nary(-*)"
            else ->         "nary(${op.name.toLowerCase()})"
        }
    }

    override fun checkArity() {
        val expect = when( op ) {
            PLUS, MIN, MAX, MULT, EQUAL, AND, OR -> -1

            POW, MINUS, DIV, MODULUS, INTDIV, LESS, LESSEQUAL,
            GREATER, GREATEREQUAL, NOTEQUAL -> 2

            PLUS_MULT, MINUS_MULT -> 3

            ABS, SIN, COS, TAN, ASIN, ATAN, SIGN, SQRT, LOG, EXP, ROUND, CEIL, FLOOR,
            SPROP, SIGMOID, SELP, LOG_NZ, NOT, ACOS -> 1
        }
        this.check(expect == -1 || expect == inputs.size) {"bad arity for $op: ${inputs.size}"}
    }

    override fun refreshSchema() {
        // union of input schemas
        schema.clear()
        inputs.forEach { schema.unionWithBound(it.schema) }
    }

    /**
     * Get how many times each label is present in the input.
     */
    fun getJoinLabelCounts(): Multiset<Name> {
        val ms = HashMultiset.create<Name>()
        inputs.forEach {
            ms.addAll(it.schema.names)
        }
        return ms
    }
}
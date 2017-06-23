package org.apache.sysml.hops.spoof2.plan

import com.google.common.collect.HashMultiset
import com.google.common.collect.Multiset
import com.google.common.collect.Multisets
import org.apache.sysml.hops.spoof2.plan.SNodeNary.NaryOp.*

class SNodeNary(
        val op: NaryOp,
        inputs: List<SNode>
) : SNode(inputs) {

    enum class NaryOp {
        //unary operations
        NOT,
        ABS, SIN, COS, TAN, ASIN, ACOS, ATAN, SIGN, SQRT, LOG, EXP,
        ROUND, CEIL, FLOOR,
        SPROP, SIGMOID, SELP, LOG_NZ,

        //binary operations
        PLUS,
        MINUS, MULT, DIV, MODULUS, INTDIV,
        LESS, LESSEQUAL, GREATER, GREATEREQUAL, EQUAL, NOTEQUAL,
        MIN, MAX, AND, OR, POW, //LOG (see unary)

        //ternary operations
        PLUS_MULT,
        MINUS_MULT,

        //reorg operations
        TRANSPOSE,

        // matrix operators
        MMULT;

        companion object {
            operator fun contains(value: String): Boolean {
                return values().any { it.name == value }
            }
        }
    }

    constructor(op: NaryOp, vararg inputs: SNode) : this(op, inputs.asList())

    override val isSchemaAggregator = false
    override val isSchemaPropagator = true

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
            TRANSPOSE ->    "nary(t)"
            else ->         "nary(${op.name.toLowerCase()})"
        }
    }

    override fun checkArity() {
        val expect = when( op ) {
            PLUS, MIN, MAX, MULT, EQUAL, AND, OR -> -1

            MMULT, POW, MINUS, DIV, MODULUS, INTDIV, LESS, LESSEQUAL,
            GREATER, GREATEREQUAL, NOTEQUAL -> 2

            PLUS_MULT, MINUS_MULT -> 3

            TRANSPOSE, ABS, SIN, COS, TAN, ASIN, ATAN, SIGN, SQRT, LOG, EXP, ROUND, CEIL, FLOOR,
            SPROP, SIGMOID, SELP, LOG_NZ, NOT, ACOS -> 1
        }
        this.check(expect == -1 || expect == inputs.size) {"bad arity for $op: ${inputs.size}"}
    }

    override fun updateSchema() {
        // union of input schema labels
        // make this more specific for the operators...
        schema.clearLabelsTypes()
        inputs.forEach { schema += it.schema }

        when( op ) {
            PLUS, MIN, MAX, MULT, EQUAL, AND, OR -> {
                val maxInputTypeNode = inputs.maxBy { it.schema.type.size }!!
                // all scalars -> scalar
                // exists a vector -> assume other vectors match orientation and dimension? Output vector
                // exists a matrix -> assume other matrices and vectors match. Output matrix
                // todo actually check these other dimensions in non-scalar cases
                schema.setType(maxInputTypeNode.schema.type, maxInputTypeNode.schema.rowVector)
            }

            MMULT -> { // 2 inputs
                val sa = inputs[0].schema
                val sb = inputs[1].schema
                this.check(sa.type.isNotEmpty() && sb.type.isNotEmpty()) {"MMULT on scalars is forbidden but given input schema types: $sa, $sb"}
                when (sa.type.size) {
                    2 -> {
                        this.check( sa.type[1] == sb.type[0] ) {"MMULT dimension mismatch: $sa, $sb"}
                        when( sb.type.size ) {
                            1 -> {
                                this.check( !sb.rowVector ) {"MMULT with row vector on right: $sa, $sb"}
                                schema.setType( sa.type[0], sb.type[0], rowVector = false )
                            }
                            2 -> schema.setType( sa.type[0], sb.type[1] )
                            else -> this.check(false) {"MMULT too many type dimensions on second input: $sa, $sb"}
                        }
                    }
                    1 -> {
                        this.check( sa.type[0] == sb.type[0] ) {"MMULT dimension mismatch: $sa, $sb"}
                        when( sb.type.size ) {
                            1 -> {
                                this.check( sa.rowVector xor sb.rowVector ) {"MMULT on vectors should not have same orientation: $sa, $sb"}
                                // inner product results in scalar; no output type dimensions
                                if( !sa.rowVector ) // outer product
                                    schema.setType( sa.type[0], sb.type[1] )
                            }
                            2 -> {
                                this.check( sa.rowVector ) {"MMULT with col vector on left: $sa, $sb"}
                                schema.setType( sa.type[0], sb.type[1], rowVector = true)
                            }
                            else -> this.check(false) {"MMULT too many type dimensions on second input: $sa, $sb"}
                        }
                    }
                    else -> this.check(false) {"MMULT too many type dimensions on first input: $sa, $sb"}
                }
            }

            POW, MINUS, DIV, MODULUS, INTDIV, LESS, LESSEQUAL,
            GREATER, GREATEREQUAL, NOTEQUAL -> {
                schema.setType(inputs[0].schema.type, inputs[0].schema.rowVector)
                // todo actually check type of other input (scalar for pow, matching or vector for minus, etc.)
            }

            PLUS_MULT, MINUS_MULT -> TODO()

            ABS, SIN, COS, TAN, ASIN, ATAN, SIGN, SQRT, LOG, EXP, ROUND, CEIL, FLOOR,
            SPROP, SIGMOID, SELP, LOG_NZ, NOT, ACOS -> schema.setType(inputs[0].schema.type, inputs[0].schema.rowVector)

            TRANSPOSE -> schema.setType(inputs[0].schema.type.reversed(), !inputs[0].schema.rowVector)
        }
    }

    /**
     * Get how many times each label is present in the input.
     */
    fun getJoinLabelCounts(): Multiset<String> {
        val ms = HashMultiset.create<String>()
        inputs.forEach {
            ms.addAll(it.schema.labels)
        }
        return ms
    }
}

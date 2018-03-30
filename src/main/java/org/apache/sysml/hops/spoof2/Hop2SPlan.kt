package org.apache.sysml.hops.spoof2

import org.apache.sysml.hops.*
import org.apache.sysml.hops.rewrite.HopRewriteUtils
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.*
import org.apache.sysml.parser.Expression
import org.apache.sysml.utils.Explain
import java.util.ArrayList

/**
 * Construct an SPlan DAG from a Hop DAG.
 * Performs one-time SPlan Rewrites.
 *
 * Todo: expand t(+*) and t(-*).
 */
object Hop2SPlan {
    private val LOG = Spoof2Compiler.LOG

    //internal configuration flags
    private const val PRINT_SNODE_CONSTRUCTION = false
    private const val CHECK = false

    private val _rulesFirstOnce: List<SPlanRewriteRule> = listOf(
            RewriteDecompose()//,          // Subtract  + and *(-1);   ^2  Self-*
            //RewriteNormalizePlusMatrixVector() // matrix + vector ==> matrix + (ones * vector) // todo decide if we need this
    )
    private val _ruleBindElim: List<SPlanRewriteRule> = listOf(
            RewriteBindElim()
    )

    fun hop2SPlan(roots: List<Hop>): ArrayList<SNode> {
        Hop.resetVisitStatus(roots)
        val snodeMemo: MutableMap<Hop, SNode> = hashMapOf()
        val sroots = roots.mapTo(ArrayList()) { rConstructSumProductPlan(it, snodeMemo) }
        Hop.resetVisitStatus(roots)

        // perform one-time Hop Rewrites
        SPlanTopDownRewriter.rewriteDown(sroots, _rulesFirstOnce)

//        if( SPlanRewriteRule.LOG.isTraceEnabled )
//            SPlanRewriteRule.LOG.trace("Before bind elim: "+ Explain.explainSPlan(sroots))

        // one-time bind elim
        var count0 = 0
        do {
            count0++
            if(CHECK) SPlanValidator.validateSPlan(sroots)
            val changed = SPlanTopDownRewriter.rewriteDown(sroots, _ruleBindElim)
        } while (changed)

//        if( SPlanRewriteRule.LOG.isTraceEnabled )
//            SPlanRewriteRule.LOG.trace("After bind elim (count=$count0): "+ Explain.explainSPlan(sroots))

        // Deal with 0
        val resultMPS = RewriteMultiplyPlusSimplify().rewriteSPlan(sroots)

        if( SPlanRewriteRule.LOG.isTraceEnabled )
            SPlanRewriteRule.LOG.trace("After MPS simplify (resultMPS=$resultMPS): "+ Explain.explainSPlan(sroots))

        return sroots
    }


    // Input Hop Dag has matrices, vectors, and scalars. No tensors here.
    //orientationMemo: MutableMap<Hop, SNode>
    private fun rConstructSumProductPlan(current: Hop, snodeMemo: MutableMap<Hop, SNode>): SNode {
        if (current.isVisited)
            return snodeMemo[current]!!

        //recursively process child nodes
        val inputs = current.input.mapTo(ArrayList()) { rConstructSumProductPlan(it, snodeMemo) }

        //construct node for current hop
        val node: SNode = when( current ) {
            is DataOp -> {
                // no binding for reads and writes
                if (current.isWrite)
                    SNodeData(current, inputs[0])
                else
                    SNodeData(current)
            }
            is LiteralOp -> {
                SNodeData(current)
            }
            is DataGenOp -> {
                SNodeExt(current, inputs)
            }
            is ReorgOp -> {
                if (HopRewriteUtils.isTransposeOperation(current)) {
                    // reverse the mapping in the unbind
                    if (inputs[0].schema.size == 2) {
                        val bindings = inputs[0].schema.genAllBindings()
                        inputs[0] = SNodeBind(inputs[0], bindings)

                        val flipBindings = mapOf(AU.U0 to bindings[AU.U1]!!, AU.U1 to bindings[AU.U0]!!)
                        SNodeUnbind(inputs[0], flipBindings)
                    } else {
                        inputs[0] // skip transpose on vector
                    }
                } else
                    SNodeExt(current, inputs)
            }
            is UnaryOp -> {
                if (current.op.name in SNodeNary.NaryOp) {
                    //ABS, SIN, COS, TAN, ASIN, ATAN, SIGN, SQRT, LOG, EXP, ROUND, CEIL, FLOOR, ...
                    //SPROP, SIGMOID, SELP, LOG_NZ, NOT, ACOS
                    val bindings = inputs[0].schema.genAllBindings()
                    if( bindings.isNotEmpty() )
                        inputs[0] = SNodeBind(inputs[0], bindings)
                    // todo - handle UnaryOps that act like SELECTs, such as diag. Equate attribute names in this case.
                    val nary = SNodeNary(SNodeNary.NaryOp.valueOf(current.op.name), inputs[0])
                    if( bindings.isNotEmpty() )
                        SNodeUnbind(nary, bindings)
                    else
                        nary
                }
                else
                    SNodeExt(current, inputs[0])
            }
            is BinaryOp -> {
                if (current.op.name in SNodeNary.NaryOp // special case + on strings
                        && !( current.valueType == Expression.ValueType.STRING && current.op == Hop.OpOp2.PLUS )) {
                    //PLUS, MIN, MAX, MULT, EQUAL, AND, OR
                    //POW, MINUS, DIV, MODULUS, INTDIV, LESS, LESSEQUAL, GREATER, GREATEREQUAL, NOTEQUAL
                    // if both scalar, no bindings
                    // if one is scalar, gen bindings for other
                    // if both are vectors, bind to same name
                    // if vector and matrix... depends on orientation of vector. Get it from the original Hop.
                    // if both are matrices, bind rows and cols to same name
                    var (i0, i1, iMap) = largerSmaller(inputs[0], inputs[1]) { it.schema.size }
                    // i0's dimension is >= i1's dimension

                    val boundNames = mutableMapOf<AU,AB>()
                    when( i0.schema.size ) {
                        0 -> {}
                        1 -> {
                            val bs = i0.schema.genAllBindings()
                            i0 = SNodeBind(i0, bs)
                            boundNames += bs
                            if( i1.schema.isNotEmpty() ) {
                                // if vector orientations match, then bind to same name
                                // otherwise we have outer product; bind to different names
                                if (current.input[0].classify() == current.input[1].classify()) {
                                    i1 = SNodeBind(i1, bs)
                                }
                                else {
                                    val bs1 = i1.schema.genAllBindings()
                                    i1 = SNodeBind(i1, bs1)
                                    boundNames += bs
                                }
                            }
                        }
                        2 -> {
                            val bs0 = i0.schema.genAllBindings()
                            i0 = SNodeBind(i0, bs0)
                            boundNames += bs0 // order of unbindings is equal to order of attributes in matrix
                            when( i1.schema.size ) {
                                0 -> {}
                                1 -> { // matrix * vector: check orientation and bind appropriately
                                    val vector = current.input[iMap[1]]
                                    val bs1 = if( vector.dim1 == 1L )
                                        mapOf(AU.U0 to bs0[AU.U1]!!) // row vector matches on cols
                                    else
                                        mapOf(AU.U0 to bs0[AU.U0]!!) // col vector matches on rows
                                    i1 = SNodeBind(i1, bs1)
                                }
                                2 -> { // matrix * matrix: bind both
                                    i1 = SNodeBind(i1, bs0)
                                }
                            }
                        }
                        else -> throw HopsException("unexpected tensor while constructing SNodes: ${i0.schema}")
                    }
                    inputs[iMap[0]] = i0
                    inputs[iMap[1]] = i1
                    val ret = SNodeNary(SNodeNary.NaryOp.valueOf(current.op.name), inputs)
                    if( boundNames.isNotEmpty() )
                        SNodeUnbind(ret, boundNames)
                    else ret
                }
                else
                    SNodeExt(current, inputs)
            }
            is AggUnaryOp -> {
                when (inputs[0].schema.size) {
                    0 -> { // aggregate a scalar?
                        inputs[0] // skip the AggUnaryOp
                    }
                    1 -> { // aggregate a vector to a scalar
                        // Hold up! We might have a trivial aggregate.
                        val nontrivial = when( current.direction ) {
                            Hop.Direction.RowCol -> true
                            Hop.Direction.Row -> current.input[0].dim2 != 1L
                            Hop.Direction.Col -> current.input[0].dim1 != 1L
                            else -> throw HopsException("bad direction ${current.direction} on (${current.hopID}) $current")
                        }
                        if( nontrivial ) {
                            val bs = inputs[0].schema.genAllBindings()
                            inputs[0] = SNodeBind(inputs[0], bs)
                            SNodeAggregate(current.op, inputs[0], bs[AU.U0]!!)
                        } else inputs[0]
                    }
                    2 -> { // aggregate a matrix; check direction
                        val bs = inputs[0].schema.genAllBindings()
                        inputs[0] = SNodeBind(inputs[0], bs)
                        when( current.direction!! ) {
                            Hop.Direction.RowCol -> {
                                SNodeAggregate(current.op, inputs[0], bs[AU.U0]!!, bs[AU.U1]!!)
                            }
                            Hop.Direction.Row -> { // sum rows ==> col vector
                                val agg = SNodeAggregate(current.op, inputs[0], bs[AU.U1]!!)
                                SNodeUnbind(agg, mapOf(AU.U0 to bs[AU.U0]!!))
                            }
                            Hop.Direction.Col -> { // sum cols ==> row vector
                                val agg = SNodeAggregate(current.op, inputs[0], bs[AU.U0]!!)
                                SNodeUnbind(agg, mapOf(AU.U0 to bs[AU.U1]!!))
                            }
                        }
                    }
                    else -> throw HopsException("unexpected tensor while constructing SNodes: ${inputs[0].schema}")
                }
            }
            is AggBinaryOp -> { // matrix multiply. There may be vectors.
                if( current.innerOp.name in SNodeNary.NaryOp) {
                    val boundNames = mutableMapOf<AU,AB>()
                    val aggName: AB?
                    when (current.input[0].classify()) {
                        HopClass.SCALAR -> {
                            // possibility of 1x1 times 1xk -- in this case we should use a regular multiply
                            when( current.input[1].classify() ) {
                                HopClass.ROW_VECTOR -> {
                                    val bs0 = inputs[1].schema.genAllBindings()
                                    inputs[1] = SNodeBind(inputs[1], bs0)
                                    boundNames += AU.U0 to bs0[AU.U0]!!
                                }
                                HopClass.SCALAR -> {}
                                else -> throw HopsException("AggBinaryOp id=${current.hopID} on scalar and ${current.input[1].classify()}; inputs are $inputs")
                            }
                            aggName = null
                        }
                        HopClass.COL_VECTOR -> {
                            HopsException.check(current.input[1].classify() == HopClass.ROW_VECTOR
                                    || current.input[1].classify() == HopClass.SCALAR, current,
                                    "Column vector on left must multiply with row vector on right")
                            // outer product
                            val bs0 = inputs[0].schema.genAllBindings()
                            //LOG.warn("bs0 is $bs0; current.inputs[0] is ${current.input[0]} ${inputs[0]} ${inputs[0].schema} dim1=${current.input[0].dim1} dim2=${current.input[0].dim2}")
                            inputs[0] = SNodeBind(inputs[0], bs0)
                            boundNames += AU.U0 to bs0[AU.U0]!! //(inputs[0].schema.names.first() as AB)
                            if( inputs[1].schema.isNotEmpty() ) { // check for multiply with scalar
                                val bs1 = inputs[1].schema.genAllBindings()
                                inputs[1] = SNodeBind(inputs[1], bs1)
                                boundNames += AU.U1 to bs1[AU.U0]!!
                            }
                            aggName = null
                        }
                        HopClass.ROW_VECTOR, HopClass.MATRIX -> {
                            val rightClass = current.input[1].classify()
                            HopsException.check(rightClass == HopClass.COL_VECTOR ||
                                    rightClass == HopClass.MATRIX, current,
                                    "Row vector or Matrix on left must multiply with col vector or matrix on right")
                            val bs0 = inputs[0].schema.genAllBindings()
                            inputs[0] = SNodeBind(inputs[0], bs0)
                            // bind last name of inputs[0] to first name of inputs[1]
                            aggName = bs0[Attribute.Unbound(inputs[0].schema.size - 1)]!!
                            val bs1 = mutableMapOf(AU.U0 to aggName)
                            inputs[1].schema.fillWithBindings(bs1) // match row vector binding with first dim on inputs[1]
                            inputs[1] = SNodeBind(inputs[1], bs1)
                            if( inputs[0].schema.size == 2 ) boundNames += AU.U0 to bs0[AU.U0]!!
                            if( inputs[1].schema.size == 2 ) boundNames += Attribute.Unbound(boundNames.size) to bs1[AU.U1]!!
                        }
                    }
                    var ret: SNode = SNodeNary(SNodeNary.NaryOp.valueOf(current.innerOp.name), inputs)
                    if( aggName != null ) {
                        ret = SNodeAggregate(current.outerOp, ret, aggName)
                    }
                    if( boundNames.isNotEmpty() ) SNodeUnbind(ret, boundNames) else ret
                }
                else
                    SNodeExt(current, inputs)
            }
            else -> {
                SNodeExt(current, inputs)
//                throw RuntimeException("Error constructing SNode for HOP: ${current.hopID} ${current.opString}.")
            }
        }

        current.setVisited()
        snodeMemo.put(current, node)
        if( PRINT_SNODE_CONSTRUCTION && LOG.isInfoEnabled )
            LOG.info("compile (${current.hopID}) $current dim1=${current.dim1} dim2=${current.dim2} as (${node.id}) $node ${node.schema} ${node.inputs}")
        return node
    }

}
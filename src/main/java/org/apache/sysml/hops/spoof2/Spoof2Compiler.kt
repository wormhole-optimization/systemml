package org.apache.sysml.hops.spoof2

import java.util.ArrayList
import java.util.Arrays

import org.apache.commons.logging.LogFactory
import org.apache.log4j.Level
import org.apache.log4j.Logger
import org.apache.sysml.hops.AggBinaryOp
import org.apache.sysml.hops.AggUnaryOp
import org.apache.sysml.hops.BinaryOp
import org.apache.sysml.hops.DataGenOp
import org.apache.sysml.hops.DataOp
import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.Hop.OpOp1
import org.apache.sysml.hops.Hop.OpOp2
import org.apache.sysml.hops.Hop.OpOp3
import org.apache.sysml.hops.HopsException
import org.apache.sysml.hops.LiteralOp
import org.apache.sysml.hops.ReorgOp
import org.apache.sysml.hops.UnaryOp
import org.apache.sysml.hops.rewrite.HopDagValidator
import org.apache.sysml.hops.rewrite.HopRewriteUtils
import org.apache.sysml.hops.rewrite.ProgramRewriteStatus
import org.apache.sysml.hops.rewrite.ProgramRewriter
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.plan.SNodeNary.NaryOp
import org.apache.sysml.hops.spoof2.rewrite.BasicSPlanRewriter
import org.apache.sysml.parser.*
import org.apache.sysml.runtime.DMLRuntimeException
import org.apache.sysml.utils.Explain


object Spoof2Compiler {
    private val LOG = LogFactory.getLog(Spoof2Compiler::class.java.name)

        //internal configuration flags
        const val LDEBUG = true
        // for internal debugging only
        init {
            if (LDEBUG) Logger.getLogger("org.apache.sysml.hops.spoof2").level = Level.TRACE
        }

        // todo inefficient; might be fine just to check the top-level sizes
        fun allKnownSizes(hop: Hop): Boolean {
            if (!hop.dimsKnown())
                return false
            return hop.input.all { allKnownSizes(it) }
        }

    @JvmStatic
    @Throws(LanguageException::class, HopsException::class, DMLRuntimeException::class)
    fun generateCode(dmlprog: DMLProgram) {
        // for each namespace, handle function statement blocks
        for (namespaceKey in dmlprog.namespaces.keys) {
            for (fname in dmlprog.getFunctionStatementBlocks(namespaceKey).keys) {
                val fsblock = dmlprog.getFunctionStatementBlock(namespaceKey, fname)
                generateCodeFromStatementBlock(fsblock)
            }
        }

        // handle regular statement blocks in "main" method
        for (i in 0..dmlprog.numStatementBlocks - 1) {
            val current = dmlprog.getStatementBlock(i)
            generateCodeFromStatementBlock(current)
        }
    }

    @Throws(HopsException::class, DMLRuntimeException::class)
    fun generateCodeFromStatementBlock(current: StatementBlock) {
        when( current ) {
            is FunctionStatementBlock -> {
                val fstmt = current.getStatement(0) as FunctionStatement
                for (sb in fstmt.body)
                    generateCodeFromStatementBlock(sb)
            } 
            is WhileStatementBlock -> {
                val wsb = current
                val wstmt = wsb.getStatement(0) as WhileStatement
                wsb.predicateHops = optimize(wsb.predicateHops, false)
                for (sb in wstmt.body)
                    generateCodeFromStatementBlock(sb)
            } 
            is IfStatementBlock -> {
                val isb = current
                val istmt = isb.getStatement(0) as IfStatement
                isb.predicateHops = optimize(isb.predicateHops, false)
                for (sb in istmt.ifBody)
                    generateCodeFromStatementBlock(sb)
                for (sb in istmt.elseBody)
                    generateCodeFromStatementBlock(sb)
            } 
            is ForStatementBlock -> { //incl parfor
                val fsb = current
                val fstmt = fsb.getStatement(0) as ForStatement
                fsb.fromHops = optimize(fsb.fromHops, false)
                fsb.toHops = optimize(fsb.toHops, false)
                fsb.incrementHops = optimize(fsb.incrementHops, false)
                for (sb in fstmt.body)
                    generateCodeFromStatementBlock(sb)
            } 
            else -> { //generic (last-level)
                current._hops = generateCodeFromHopDAGs(current._hops)
                current.updateRecompilationFlag()
            }
        }
    }

    @Throws(HopsException::class, DMLRuntimeException::class)
    fun generateCodeFromHopDAGs(roots: ArrayList<Hop>?): ArrayList<Hop>? {
        if (roots == null)
            return null

        val optimized = optimize(roots, false)
        Hop.resetVisitStatus(roots)
        Hop.resetVisitStatus(optimized)

        return optimized
    }

    /**
     * Main interface of sum-product optimizer, predicate dag.

     * @param root      dag root node
     * @param recompile true if invoked during dynamic recompilation
     * @return dag root node of modified dag
     * @throws DMLRuntimeException if optimization failed
     * @throws HopsException       -
     */
    @Throws(DMLRuntimeException::class, HopsException::class)
    fun optimize(root: Hop?, recompile: Boolean): Hop? {
        if (root == null)
            return null
        return optimize(ArrayList(Arrays.asList(root)), recompile).get(0)
    }

    /**
     * Main interface of sum-product optimizer, statement block dag.

     * @param roots dag root nodes
     * @param recompile true if invoked during dynamic recompilation
     * @return dag root nodes of modified dag
     * @throws DMLRuntimeException if optimization failed
     * @throws HopsException -
     */
    @Throws(DMLRuntimeException::class, HopsException::class)
    fun optimize(roots: ArrayList<Hop>, recompile: Boolean): ArrayList<Hop> {
        if (LOG.isTraceEnabled) {
            LOG.trace("Spoof2Compiler called for HOP DAG: \n" + Explain.explainHops(roots))
        }

        // if any sizes unknown, don't do Spoof2
        if( roots.any { !allKnownSizes(it)} ) {
            if (LOG.isTraceEnabled) {
                LOG.trace("Skipping Spoof2 due to unknown sizes")
            }
            return roots
        }

        //construct sum-product plan
        var sroots = ArrayList<SNode>()
        Hop.resetVisitStatus(roots)
        val snodeMemo: MutableMap<Hop, SNode> = hashMapOf()
        for (root in roots)
            sroots.add(rConstructSumProductPlan(root, snodeMemo))

        if (LOG.isTraceEnabled) {
            LOG.trace("Explain after initial SPlan construction: " + Explain.explainSPlan(sroots))
        }

        //rewrite sum-product plan
        val rewriter = BasicSPlanRewriter()
        sroots = rewriter.rewriteSPlan(sroots)

        if (LOG.isTraceEnabled) {
            LOG.trace("Explain after SPlan rewriting: " + Explain.explainSPlan(sroots))
        }

        //re-construct modified HOP DAG
        var roots2 = ArrayList<Hop>()
        SNode.resetVisited(sroots)
        val hopMemo: MutableMap<SNode, Hop> = hashMapOf()
        for (sroot in sroots)
            roots2.add(rReconstructHopDag(sroot, hopMemo))

        if (LOG.isTraceEnabled) {
            LOG.trace("Spoof2Compiler created modified HOP DAG: \n" + Explain.explainHops(roots2))
        }
        HopDagValidator.validateHopDag(roots2)

        //rewrite after applied sum-product optimizer
        Hop.resetVisitStatus(roots2)
        val rewriter2 = ProgramRewriter(true, true)
        roots2 = rewriter2.rewriteHopDAGs(roots2, ProgramRewriteStatus())

        if (LOG.isTraceEnabled) {
            LOG.trace("Spoof2Compiler rewritten modified HOP DAG: \n" + Explain.explainHops(roots2))
        }

        return roots2
    }


    private fun createTransposePermutation(names: Collection<Name>): Map<Name,Name> {
        require(names.size <= 2) {"transpose is undefined on tensors; given names $names"}
        if (names.size <= 1) return mapOf()
        val iter = names.iterator()
        val n1 = iter.next()
        val n2 = iter.next()
        return mapOf(n1 to n2, n2 to n1)
    }




    // Input Hop Dag has matrices, vectors, and scalars. No tensors here.
    //orientationMemo: MutableMap<Hop, SNode>
    private fun rConstructSumProductPlan(current: Hop, snodeMemo: MutableMap<Hop, SNode>): SNode {
        if (current.isVisited)
            return snodeMemo[current]!!

        //recursively process child nodes
        val inputs = current.input.mapTo(ArrayList<SNode>()) { rConstructSumProductPlan(it, snodeMemo) }

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
                    // transpose does not logically effect anything, but it will change the order of input shapes
                    // which affects the join conditions of parent binary hops, so we keep the Permute SNode.
                    // U - tr - B - inputs[0]
                    val bindings = inputs[0].schema.genAllBindings()
                    inputs[0] = SNodeBind(inputs[0], bindings)
                    val perm = SNodePermute(inputs[0], createTransposePermutation(bindings.values))
                    val U = SNodeUnbind(perm, bindings.values)
//                    // this is a trick for reading orientation from unbound attribute names
//                    // it will go away on next refreshSchema()
//                    if (U.schema.size == 1) {
//                        when( U.schema.names[0].first() ) {
//                            Schema.NamePrefix.ROW.prefixChar -> U.schema.names[0] = Schema.NamePrefix.COL.prefixStr
//                            Schema.NamePrefix.COL.prefixChar -> U.schema.names[0] = Schema.NamePrefix.ROW.prefixStr
//                        }
//                    }
                    U
                } else
                    SNodeExt(current, inputs)
            }
            is UnaryOp -> {
                if (current.op.name in NaryOp) {
                    //ABS, SIN, COS, TAN, ASIN, ATAN, SIGN, SQRT, LOG, EXP, ROUND, CEIL, FLOOR, ...
                    //SPROP, SIGMOID, SELP, LOG_NZ, NOT, ACOS
                    val bindings = inputs[0].schema.genAllBindings()
                    if( bindings.isNotEmpty() )
                        inputs[0] = SNodeBind(inputs[0], bindings)
                    // todo - handle UnaryOps that act like SELECTs, such as diag. Equate attribute names in this case.
                    val nary = SNodeNary(NaryOp.valueOf(current.op.name), inputs[0])
                    if( bindings.isNotEmpty() )
                        SNodeUnbind(nary, bindings.values)
                    else
                        nary
                }
                else
                    SNodeExt(current, inputs[0])
            }
            is BinaryOp -> {
                if (current.op.name in NaryOp) {
                    //PLUS, MIN, MAX, MULT, EQUAL, AND, OR
                    //POW, MINUS, DIV, MODULUS, INTDIV, LESS, LESSEQUAL, GREATER, GREATEREQUAL, NOTEQUAL
                    // if both scalar, no bindings
                    // if one is scalar, gen bindings for other
                    // if both are vectors, bind to same name
                    // if vector and matrix... depends on orientation of vector. Get it from the original Hop.
                    // if both are matrices, bind rows and cols to same name
                    var (i0, i1, iMap) = largerSmaller(inputs[0], inputs[1]) {it.schema.size}
                    // i0's dimension is >= i1's dimension

                    val boundNames = arrayListOf<Name>()
                    when( i0.schema.size ) {
                        0 -> {}
                        1 -> {
                            val bs = i0.schema.genAllBindings()
                            i0 = SNodeBind(i0, bs)
                            boundNames += bs.values
                            if( i1.schema.isNotEmpty() ) {
                                // both vectors: bind to same name
                                i1 = SNodeBind(i1, bs)
                            }
                        }
                        2 -> {
                            val bs0 = i0.schema.genAllBindings()
                            i0 = SNodeBind(i0, bs0)
                            boundNames += bs0.values
                            when( i1.schema.size ) {
                                0 -> {}
                                1 -> { // matrix * vector: check orientation and bind appropriately
                                    val vector = current.input[iMap[1]]
                                    val bs1 = if( vector.dim1 == 1L )
                                        mapOf(0 to bs0[1]!!) // row vector matches on cols
                                    else
                                        mapOf(0 to bs0[0]!!) // col vector matches on rows
                                    i1 = SNodeBind(i1, bs1)
                                }
                                2 -> { // matrix * matrix: bind both
                                    i1 = SNodeBind(i1, bs0)
                                }
                            }
                        }
                        else -> throw HopsException("unexpected tensor while constructing SNodes: ${i0.schema}")
                    }
                    inputs[0] = i0
                    inputs[1] = i1
                    val ret = SNodeNary(NaryOp.valueOf(current.op.name), inputs)
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
                        val bs = inputs[0].schema.genAllBindings()
                        inputs[0] = SNodeBind(inputs[0], bs)
                        SNodeAggregate(current.op, inputs[0], bs[0]!!)
                    }
                    2 -> { // aggregate a matrix; check direction
                        val bs = inputs[0].schema.genAllBindings()
                        inputs[0] = SNodeBind(inputs[0], bs)
                        when( current.direction!! ) {
                            Hop.Direction.RowCol -> {
                                SNodeAggregate(current.op, inputs[0], bs[0]!!, bs[1]!!)
                            }
                            Hop.Direction.Row -> { // sum rows ==> col vector
                                val agg = SNodeAggregate(current.op, inputs[0], bs[1]!!)
                                SNodeUnbind(agg, listOf(bs[0]!!))
                            }
                            Hop.Direction.Col -> { // sum cols ==> row vector
                                val agg = SNodeAggregate(current.op, inputs[0], bs[0]!!)
                                SNodeUnbind(agg, listOf(bs[1]!!))
                            }
                        }
                    }
                    else -> throw HopsException("unexpected tensor while constructing SNodes: ${inputs[0].schema}")
                }
            }
            is AggBinaryOp -> { // matrix multiply. There may be vectors.
                if( current.innerOp.name in NaryOp ) {
                    val boundNames = mutableSetOf<Name>()
                    val aggName: Name?
                    when (current.input[0].classify()) {
                        HopClass.SCALAR -> throw HopsException("AggBinaryOp id=${current.hopID} should not act on scalars but input SNodes are $inputs")
                        HopClass.COL_VECTOR -> {
                            HopsException.check(current.input[1].classify() == HopClass.ROW_VECTOR, current,
                                    "Column vector on left must multiply with row vector on right")
                            // outer product
                            val bs0 = inputs[0].schema.genAllBindings()
                            inputs[0] = SNodeBind(inputs[0], bs0)
                            boundNames += bs0.values
                            val bs1 = inputs[1].schema.genAllBindings()
                            inputs[1] = SNodeBind(inputs[1], bs1)
                            boundNames += bs1.values
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
                            aggName = bs0[inputs[0].schema.size - 1]!!
                            val bs1 = mutableMapOf(0 to aggName)
                            inputs[1].schema.fillWithBindings(bs1) // match row vector binding with first dim on inputs[1]
                            inputs[1] = SNodeBind(inputs[1], bs1)
                            boundNames += bs0.values.toSet() + bs1.values
                        }
                    }
                    var ret: SNode = SNodeNary(NaryOp.valueOf(current.innerOp.name), inputs)
                    if( aggName != null ) {
                        ret = SNodeAggregate(current.outerOp, ret, aggName)
                        boundNames -= aggName
                    }
                    SNodeUnbind(ret, boundNames)
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

        return node
    }

    private fun reconstructAggregate(agg: SNodeAggregate, expectBind: Boolean, hopMemo: MutableMap<SNode, Hop>): Hop {
        val mult = agg.inputs[0]
        return if( mult is SNodeNary && mult.op == NaryOp.MULT && agg.op == Hop.AggOp.SUM
                && mult.inputs.size == 2
                && agg.aggreateNames.size == 1 ) {
            // MxM
            val mult0 = mult.inputs[0]
            val mult1 = mult.inputs[1]
            val (hop0, hop1) = if( expectBind ) {
                if (mult0 !is SNodeBind || mult1 !is SNodeBind)
                    TODO("fuse a matrix multiply with further SNodes $mult0, $mult1")
                rReconstructHopDag(mult0.inputs[0], hopMemo) to rReconstructHopDag(mult1.inputs[0], hopMemo)
            } else {
                // Even if not expecting a Bind on the inputs,
                // we may have a Bind anyway because the output is a scalar (thus no Unbind)
                // but the inputs are non-scalars (and are therefore Bound)
                val m0 = if( mult0 is SNodeBind ) mult0.inputs[0] else mult0
                val m1 = if( mult1 is SNodeBind ) mult1.inputs[0] else mult1
                rReconstructHopDag(m0, hopMemo) to rReconstructHopDag(m1, hopMemo)
            }

            // AggBinaryOp always expects matrix inputs
            val h0 = if( hop0.dataType == Expression.DataType.SCALAR )
                HopRewriteUtils.createUnary(hop0, OpOp1.CAST_AS_SCALAR)
            else hop0
            val h1 = if( hop1.dataType == Expression.DataType.SCALAR )
                HopRewriteUtils.createUnary(hop1, OpOp1.CAST_AS_SCALAR)
            else hop1

            val mxm = HopRewriteUtils.createMatrixMultiply(h0, h1)
            mxm
//                            HopRewriteUtils.createUnary(mxm, OpOp1.CAST_AS_SCALAR) // why do we need this?
//            checkCastScalar(mxm)
        } else {
            val aggInput = mult
            var hop0 = if( expectBind ) {
                if (aggInput !is SNodeBind)
                    TODO("fuse an aggregate with further SNode $aggInput")
                rReconstructHopDag(aggInput.inputs[0], hopMemo)
            } else {
                // Like above, we may have a Bind
                val ai = if( aggInput is SNodeBind ) aggInput.inputs[0] else aggInput
                rReconstructHopDag(ai, hopMemo)
            }

            // AggUnaryOp always requires MATRIX input
            if( hop0.dataType == Expression.DataType.SCALAR )
                hop0 = HopRewriteUtils.createUnary(hop0, OpOp1.CAST_AS_SCALAR)

            // get direction from schema
            SNodeException.check(agg.aggreateNames.size == 1 || agg.aggreateNames.size == 2, agg) {"don't know how to compile aggregate with aggregates ${agg.aggreateNames}"}
            val dir = if( agg.aggreateNames.size == 2 )
                Hop.Direction.RowCol
            else if( hop0.dim2 == 1L )
                Hop.Direction.Col // sum first dimension ==> row vector
            else if( hop0.dim1 == 1L )
                Hop.Direction.Row // sum second dimension ==> col vector
            else if( agg.aggreateNames[0] == aggInput.schema.names[0] ) {
                agg.check(aggInput.schema.size == 2) {"this may be erroneous if aggInput is not a matrix"}
                Hop.Direction.Col
            }
            else {
                agg.check(aggInput.schema.size == 2) {"this may be erroneous if aggInput is not a matrix"}
                Hop.Direction.Row
            }

            val fin = HopRewriteUtils.createAggUnaryOp(hop0, agg.op, dir)
            fin //checkCastScalar(fin)
        }
    }

    // cast matrix to scalar
    // sometimes this is necessary, sometimes not
    // code in the SNodeExt reconstruct to Hop block checks for duplicate CAST_AS_SCALAR
    private fun checkCastScalar(hop: Hop): Hop {
        return if( hop.dimsKnown() && hop.dim1 == 1L && hop.dim2 == 1L && hop.dataType == Expression.DataType.MATRIX )
            HopRewriteUtils.createUnary(hop, OpOp1.CAST_AS_SCALAR)
        else
            hop
    }

    private fun reconstructNary(nary: SNodeNary, expectBind: Boolean, hopMemo: MutableMap<SNode, Hop>): Hop {
        var foundBind = false
        val hopInputs = nary.inputs.map { input ->
//            if( expectBind ) {
                val i = if (input is SNodeBind) input.inputs[0] else input
                rReconstructHopDag(i, hopMemo)
//            } else {
//                rReconstructHopDag(input, hopMemo)
//            }
        }
        return when( nary.inputs.size ) {
            1 -> HopRewriteUtils.createUnary(hopInputs[0], OpOp1.valueOf(nary.op.name))
            2 -> HopRewriteUtils.createBinary(hopInputs[0], hopInputs[1], OpOp2.valueOf(nary.op.name))
            3 -> HopRewriteUtils.createTernary(hopInputs[0], hopInputs[1], hopInputs[2], OpOp3.valueOf(nary.op.name))
            else -> throw SNodeException(nary, "don't know how to reconstruct a Hop from an nary with ${nary.inputs.size} inputs $nary")
        }
    }


    // Only these SNodes can have multiple parents---Unbind, Data, Ext---unless we have a scalar, in which case any SNode can appear.
    // (Also, an Nary could have a matrix input and scalar input.)
    // Start with one of these at the top. If Unbind, continue through the Binds at the bottom. This is a block.
    // We will reconstruct the whole block at once.
    // Induction: first reconstruct the children below the block.
    // Then map the block to a Hop. (Fused Op or Regular Hop)
    private fun rReconstructHopDag(current: SNode, hopMemo: MutableMap<SNode, Hop>): Hop {
        if (current.visited) {
            return hopMemo[current]!!
        }

        val node: Hop = when( current ) {
            is SNodeData -> {
                //recursively process child nodes
                val inputs = current.inputs.map { rReconstructHopDag(it, hopMemo) }
                if (inputs.isNotEmpty()) {
                    HopRewriteUtils.replaceChildReference(current.hop,
                            current.hop.input[0], inputs[0], 0)
                }
//                current.hop.parent.clear()
                current.hop.resetVisitStatus() // visit status may be set from SNode construction
                current.hop
            }
            is SNodeExt -> {
                var inputs = current.inputs.map { rReconstructHopDag(it, hopMemo) }
                current.hop.resetVisitStatus() // visit status may be set from SNode construction
//                current.hop.parent.clear() // scrap parents from old Hop Dag

                // prevent duplicate CAST_AS_SCALAR
//                if( current.hop is UnaryOp && current.hop.op == OpOp1.CAST_AS_SCALAR
//                        && inputs[0] is UnaryOp && (inputs[0] as UnaryOp).op == OpOp1.CAST_AS_SCALAR ) {
//                    inputs = inputs[0].input
//                    inputs[0].parent.clear()
//                }
                if( current.hop is UnaryOp && current.hop.op == OpOp1.CAST_AS_SCALAR
                        && inputs[0].dataType == Expression.DataType.SCALAR ) {
                    // skip the cast
                    inputs[0]
                }
                else if( current.hop is UnaryOp && current.hop.op == OpOp1.CAST_AS_MATRIX
                        && inputs[0].dataType == Expression.DataType.MATRIX ) {
                    // skip the cast
                    inputs[0]
                }
                else {
                    if (inputs.isNotEmpty()) { //robustness datagen
                        HopRewriteUtils.removeAllChildReferences(current.hop)
                        for (c in inputs)
                            current.hop.addInput(c)
                    }
                    current.hop
                }
            }
            is SNodeAggregate -> reconstructAggregate(current, false, hopMemo)
            is SNodePermute -> throw SNodeException(current, "should not be a permute on a scalar schema type")
            is SNodeNary -> reconstructNary(current, false, hopMemo)
            is SNodeUnbind -> {
                // match on the SNode beneath SNodeUnbind. Go to the Binds that are children to this block.
                val bu = current.inputs[0]
                when( bu ) {
                    is SNodeAggregate -> reconstructAggregate(bu, true, hopMemo)
                    is SNodePermute -> {
                        val perm = bu
                        val bind = perm.inputs[0]
                        if( bind !is SNodeBind )
                            TODO("fuse a transpose (permute) with further SNode $bind")
                        val bindBelow = rReconstructHopDag(bind.inputs[0], hopMemo)
                        HopRewriteUtils.createTranspose(bindBelow)
                    }
                    is SNodeNary -> reconstructNary(bu, true, hopMemo)
                    else -> throw SNodeException("don't know how to translate $bu")
                }
            }
            else -> throw SNodeException(current, "should not be able to recurse on this type of SNode")
        }

        current.visited = true
        hopMemo.put(current, node)

        return node
    }
}
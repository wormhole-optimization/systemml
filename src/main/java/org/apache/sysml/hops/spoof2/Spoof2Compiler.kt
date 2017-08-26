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
import org.apache.sysml.hops.rewrite.*
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.plan.SNodeNary.NaryOp
import org.apache.sysml.hops.spoof2.rewrite.SPlanNormalFormRewriter
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriter
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

    @JvmStatic
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
                wsb.predicateHops = optimize(wsb.predicateHops, false, true)
                for (sb in wstmt.body)
                    generateCodeFromStatementBlock(sb)
            } 
            is IfStatementBlock -> {
                val isb = current
                val istmt = isb.getStatement(0) as IfStatement
                isb.predicateHops = optimize(isb.predicateHops, false, true)
                for (sb in istmt.ifBody)
                    generateCodeFromStatementBlock(sb)
                for (sb in istmt.elseBody)
                    generateCodeFromStatementBlock(sb)
            } 
            is ForStatementBlock -> { //incl parfor
                val fsb = current
                val fstmt = fsb.getStatement(0) as ForStatement
                fsb.fromHops = optimize(fsb.fromHops, false, true)
                fsb.toHops = optimize(fsb.toHops, false, true)
                fsb.incrementHops = optimize(fsb.incrementHops, false, true)
                for (sb in fstmt.body)
                    generateCodeFromStatementBlock(sb)
            } 
            else -> { //generic (last-level)
                current._hops = generateCodeFromHopDAGs(current._hops, false, true)
                current.updateRecompilationFlag()
            }
        }
    }

    @JvmStatic
    @Throws(HopsException::class, DMLRuntimeException::class)
    fun generateCodeFromHopDAGs(roots: ArrayList<Hop>?, recompile: Boolean, doDynamicProgramRewriter: Boolean): ArrayList<Hop>? {
        if (roots == null)
            return null

        val optimized = optimize(roots, recompile, doDynamicProgramRewriter)
//        Hop.resetVisitStatus(roots)
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
    @JvmStatic
    @Throws(DMLRuntimeException::class, HopsException::class)
    fun optimize(root: Hop?, recompile: Boolean, doDynamicProgramRewriter: Boolean): Hop? {
        if (root == null)
            return null
        return optimize(ArrayList(Arrays.asList(root)), recompile, doDynamicProgramRewriter).get(0)
    }

    private fun programRewriteHops(roots: ArrayList<Hop>, recompile: Boolean,
                                   doDynamicProgramRewriter: Boolean): ArrayList<Hop> {
        Hop.resetVisitStatus(roots)
//        initial compile          ==>  CSE; SumProduct; static + dynamic ProgramWriter
//        recompile, inplace=false ==>  CSE; SumProduct; dynamic ProgramWriter
//        recompile, inplace=true  ==>  CSE; SumProduct
//        LOG.trace("Call ProgramRewriter with static=${!recompile} dynamic=$doDynamicProgramRewriter")
        val rewriter2 = ProgramRewriter(!recompile, doDynamicProgramRewriter)
            // todo - some fix with handling literals in predicates, as exposed by CSE in static rewrites during recompile - need fix from master
        rewriter2.rewriteHopDAGs(roots, ProgramRewriteStatus())
        Hop.resetVisitStatus(roots)
        return roots
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
    fun optimize(roots: ArrayList<Hop>, recompile: Boolean, doDynamicProgramRewriter: Boolean): ArrayList<Hop> {

        if( !doDynamicProgramRewriter && roots.any { it !is DataOp } ) {
            // Todo: better handling of dynamic recompile during inplace. What is safe to change during recompile?
            // GLMDML fails to converge if this is not handled carefully.
            if( LOG.isTraceEnabled )
                LOG.trace("Skipping due to inplace recompile setting")
            return roots
        }

        // if any sizes unknown, don't do Spoof2
        if( roots.any { !allKnownSizes(it)} ) {
            if (LOG.isTraceEnabled) {
                LOG.trace("Skipping Spoof2 due to unknown sizes")
            }
            return programRewriteHops(roots, recompile, doDynamicProgramRewriter)
        }

        ProgramRewriter(RewriteCommonSubexpressionElimination()).rewriteHopDAGs(roots, ProgramRewriteStatus())

        if (LOG.isTraceEnabled) {
            LOG.trace("Spoof2Compiler called for HOP DAG${if(recompile) " at RECOMPILE" else ""}: \n" + Explain.explainHops(roots))
        }

        // remember top-level orientations
        val rootClasses = roots.map(Hop::classify)

        HopDagValidator.validateHopDag(roots)

        //construct sum-product plan
        var sroots = ArrayList<SNode>()
        Hop.resetVisitStatus(roots)
        val snodeMemo: MutableMap<Hop, SNode> = hashMapOf()
        for (root in roots)
            sroots.add(rConstructSumProductPlan(root, snodeMemo))
        Hop.resetVisitStatus(roots)

        // if this is entirely composed of Data and Ext ops, then don't do Spoof2 because nothing to do
        if( sroots.all { it.isEntirelyDataExtEquals() } ) {
            if (LOG.isTraceEnabled) {
                LOG.trace("Skipping Spoof2 on DAG that is entirely composed of Data, Ext, and == nodes")
            }
            return programRewriteHops(roots, recompile, doDynamicProgramRewriter)
        }


//        BasicSPlanRewriter().rewriteSPlan(sroots, listOf(RewriteBindElim()))
        if (LOG.isTraceEnabled) {
            LOG.trace("Explain after initial SPlan construction: " + Explain.explainSPlan(sroots))
//            LOG.trace("Explain after SPlan construction and RewriteBindElim: " + Explain.explainSPlan(sroots))
        }

        //rewrite sum-product plan
        val rewriter = SPlanNormalFormRewriter()
        val rewriterResult = rewriter.rewriteSPlan(sroots)
        when( rewriterResult ) {
            is SPlanRewriter.RewriterResult.NewRoots -> sroots = rewriterResult.newRoots
            SPlanRewriter.RewriterResult.NoChange -> {}
        }

//        if (LOG.isTraceEnabled) {
//            LOG.trace("Explain after SPlan rewriting: " + Explain.explainSPlan(sroots))
//        }

        //re-construct modified HOP DAG
        var roots2 = ArrayList<Hop>()
        SNode.resetVisited(sroots)
        val hopMemo: MutableMap<SNode, Hop> = hashMapOf()
        for (sroot in sroots)
            roots2.add(rReconstructHopDag(sroot, hopMemo))

        // add transposes if necessary to roots in order to maintain same orientation as original
        // shouldn't be necessary because the roots are generally Writes, which correct orientation on their own
        roots2.mapInPlaceIndexed { idx, root2 ->
            if( rootClasses[idx].isVector && root2.classify() != rootClasses[idx] ) {
                check( root2.classify().isVector ) {"root changed type after reconstruction? Old type ${rootClasses[idx]}; new type ${root2.classify()} dims ${root2.dim1}, ${root2.dim2} hopid=${root2.hopID}" +
                        "\n modified Hop Dag is:\n" + Explain.explainHops(roots2)}
                // todo look at transposes
                if( LOG.isTraceEnabled )
                    LOG.trace("creating root transpose at root $idx to enforce orientation ${rootClasses[idx]}")
                HopRewriteUtils.createTranspose(root2)
            }
            else
                root2
        }

        // during recompile, we may need to do inplace updates. If so, we must use the original Hop roots.
        // Todo: proper handling of dynamic recompile
        if( !doDynamicProgramRewriter ) {
            if( roots.size != roots2.size )
                throw RuntimeException("changed the number of roots during recompile from $roots to $roots2")
            roots.mapInPlaceIndexed { rootNum, root ->
                val root2 = roots2[rootNum]
                root.input.mapInPlaceIndexed { inPos, _ ->
                    val newInput = root2.input[inPos]
                    newInput.parent[newInput.parent.indexOf(root2)] = root
                    newInput
                }
                root
            }
            roots2 = roots
        }

        if (LOG.isTraceEnabled) {
            LOG.trace("Spoof2Compiler created modified HOP DAG: \n" + Explain.explainHops(roots2))
        }
        HopDagValidator.validateHopDag(roots2)

        //rewrite after applied sum-product optimizer
        programRewriteHops(roots2, recompile, doDynamicProgramRewriter)
//        if( doDynamicProgramRewriter )
//            RewriteAlgebraicSimplificationDynamic().rewriteHopDAGs(roots2, ProgramRewriteStatus())

        HopDagValidator.validateHopDag(roots2)

        if (LOG.isTraceEnabled) {
            LOG.trace("Spoof2Compiler rewritten modified HOP DAG: \n" + Explain.explainHops(roots2))
        }

        return roots2
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
                    // reverse the mapping in the unbind
                    if (inputs[0].schema.size == 2) {
                        val bindings = inputs[0].schema.genAllBindings()
                        inputs[0] = SNodeBind(inputs[0], bindings)

                        val flipBindings = mapOf(0 to bindings[1]!!, 1 to bindings[0]!!)
                        SNodeUnbind(inputs[0], flipBindings)
                    } else {
                        inputs[0] // skip transpose on vector
                    }
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
                        SNodeUnbind(nary, bindings)
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
                    var (i0, i1, iMap) = largerSmaller(inputs[0], inputs[1]) { it.schema.size }
                    // i0's dimension is >= i1's dimension

                    val boundNames = mutableMapOf<Int,Name>()
                    when( i0.schema.size ) {
                        0 -> {}
                        1 -> {
                            val bs = i0.schema.genAllBindings()
                            i0 = SNodeBind(i0, bs)
                            boundNames += bs
                            if( i1.schema.isNotEmpty() ) {
                                // both vectors: bind to same name
                                i1 = SNodeBind(i1, bs)
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
                    inputs[iMap[0]] = i0
                    inputs[iMap[1]] = i1
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
                                SNodeUnbind(agg, mapOf(0 to bs[0]!!))
                            }
                            Hop.Direction.Col -> { // sum cols ==> row vector
                                val agg = SNodeAggregate(current.op, inputs[0], bs[0]!!)
                                SNodeUnbind(agg, mapOf(0 to bs[1]!!))
                            }
                        }
                    }
                    else -> throw HopsException("unexpected tensor while constructing SNodes: ${inputs[0].schema}")
                }
            }
            is AggBinaryOp -> { // matrix multiply. There may be vectors.
                if( current.innerOp.name in NaryOp ) {
                    val boundNames = mutableMapOf<Int,Name>()
                    val aggName: Name?
                    when (current.input[0].classify()) {
                        HopClass.SCALAR -> throw HopsException("AggBinaryOp id=${current.hopID} should not act on scalars but input SNodes are $inputs")
                        HopClass.COL_VECTOR -> {
                            HopsException.check(current.input[1].classify() == HopClass.ROW_VECTOR, current,
                                    "Column vector on left must multiply with row vector on right")
                            // outer product
                            val bs0 = inputs[0].schema.genAllBindings()
                            inputs[0] = SNodeBind(inputs[0], bs0)
                            boundNames += 0 to bs0[0]!!
                            val bs1 = inputs[1].schema.genAllBindings()
                            inputs[1] = SNodeBind(inputs[1], bs1)
                            boundNames += 1 to bs1[0]!!
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
                            if( inputs[0].schema.size == 2 ) boundNames += 0 to bs0[0]!!
                            if( inputs[1].schema.size == 2 ) boundNames += boundNames.size to bs1[1]!!
                        }
                    }
                    var ret: SNode = SNodeNary(NaryOp.valueOf(current.innerOp.name), inputs)
                    if( aggName != null ) {
                        ret = SNodeAggregate(current.outerOp, ret, aggName)
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


    private fun reconstructAggregate(agg: SNodeAggregate, hopMemo: MutableMap<SNode, Hop>): Hop {
        val mult = agg.input

        return if( mult is SNodeNary && mult.op == NaryOp.MULT && agg.op == Hop.AggOp.SUM
                && mult.inputs.size == 2
                && mult.inputs[0].schema.names.intersect(mult.inputs[1].schema.names).size == 1 // forbear element-wise multiplication followed by agg
                && agg.aggreateNames.size == 1 )
        {   // MxM
            var mult0 = mult.inputs[0]
            var mult1 = mult.inputs[1]

            // We may have a Bind because the output is a scalar (thus no Unbind)
            // but the inputs are non-scalars (and are therefore Bound)
            var hop0 = rReconstructHopDag(mult0, hopMemo)
            var hop1 = rReconstructHopDag(mult1, hopMemo)

            // AggBinaryOp always expects matrix inputs
            if( hop0.dataType == Expression.DataType.SCALAR ) {
                hop0 = HopRewriteUtils.createUnary(hop0, OpOp1.CAST_AS_MATRIX)
                if( LOG.isTraceEnabled )
                    LOG.trace("inserted cast_as_matrix id=${hop0.hopID} for left input to AggBinaryOp")
            }
            if( hop1.dataType == Expression.DataType.SCALAR ) {
                hop1 = HopRewriteUtils.createUnary(hop1, OpOp1.CAST_AS_MATRIX)
                if( LOG.isTraceEnabled )
                    LOG.trace("inserted cast_as_matrix id=${hop1.hopID} for right input to AggBinaryOp")
            }
            agg.check(mult0.schema.size in 1..2 && mult1.schema.size in 1..2) {"matrix multiply with tensors? inputs: $mult0 $mult1"}

            // use symmetry
            if( mult0.schema.size == 2 && mult1.schema.size == 1 ) {
                val tmp = mult0; mult0 = mult1; mult1 = tmp
                val t = hop0; hop0 = hop1; hop1 = t
            }

            // check positions of labels and see if we need to transpose
            val aggName: Name = agg.aggreateNames[0]
            when( mult0.schema.size ) {
                1 -> when( mult1.schema.size ) { // hop0 is V
                    1 -> when( hop0.classify() ) { // hop1 is V; inner product
                        HopClass.ROW_VECTOR -> when( hop1.classify() ) {
                            HopClass.COL_VECTOR -> {}
                            HopClass.ROW_VECTOR -> hop1 = HopRewriteUtils.createTranspose(hop1)
                            else -> throw AssertionError()
                        }
                        HopClass.COL_VECTOR -> when( hop1.classify() ) {
                            HopClass.COL_VECTOR -> hop0 = HopRewriteUtils.createTranspose(hop0)
                            HopClass.ROW_VECTOR -> {val t = hop0; hop0 = hop1; hop1 = t}
                            else -> throw AssertionError()
                        }
                        else -> throw AssertionError()
                    }
                    2 -> { // hop1 is M; check VxM or MxV
                        // get matching name, which is also aggregated over
                        val i1 = mult1.schema.names.indexOf(aggName); agg.check(i1 != -1) {"$mult1 should have the name $aggName we are aggregating over"}
                        when( i1 ) {
                            0 -> when( hop0.classify() ) { // VxM; ensure vector is a row vector
                                HopClass.ROW_VECTOR -> {}
                                HopClass.COL_VECTOR -> hop0 = HopRewriteUtils.createTranspose(hop0) //
                                else -> throw AssertionError()
                            }
                            1 -> { // MxV; swap hops and ensure vector is a col vector
                                val t = hop0; hop0 = hop1; hop1 = t
                                when( hop1.classify() ) {
                                    HopClass.ROW_VECTOR -> hop1 = HopRewriteUtils.createTranspose(hop1)
                                    HopClass.COL_VECTOR -> {}
                                    else -> throw AssertionError()
                                }
                            }
                        }
                    }
                }
                2 -> { // MxM case
                    val i0 = mult0.schema.names.indexOf(aggName); agg.check(i0 != -1) {"$mult0 should have the name $aggName we are aggregating over"}
                    val i1 = mult1.schema.names.indexOf(aggName); agg.check(i1 != -1) {"$mult1 should have the name $aggName we are aggregating over"}
                    // make common attribute on position 1 of hop0 and position0 of hop1
                    when( i0 ) {
                        0 -> when( i1 ) {
                            0 -> hop0 = HopRewriteUtils.createTranspose(hop0)       //[b,a]x[b,c]
                            1 -> { val tmp = hop0; hop0 = hop1; hop1 = tmp     //[b,a]x[c,b]
                                // also switch the SNode plan inputs and refresh schema, for later reconstruction
                                if( LOG.isTraceEnabled )
                                    LOG.trace("Switch MxM inputs of (${mult.id}) $mult ${mult.schema}")
                                mult.inputs.reverse()
                                mult.refreshSchemasUpward() // refresh schema of all parents above, as long as schema changes
                            }
                        }
                        1 -> when( i1 ) {
                            0 -> {}                                                 //[a,b]x[b,c]
                            1 -> hop1 = HopRewriteUtils.createTranspose(hop1)       //[a,b]x[c,b]
                        }
                    }
                }
            }
            var mxm: Hop = HopRewriteUtils.createMatrixMultiply(hop0, hop1)
            if( mxm.dim1 == 1L && mxm.dim2 == 1L ) {
                if( LOG.isDebugEnabled )
                    LOG.debug("Casting result of matrix multiply ${mxm.hopID} to scalar")
                mxm = HopRewriteUtils.createUnary(mxm, OpOp1.CAST_AS_SCALAR)
            }
            mxm
        }
        else { // general Agg
            val aggInput = mult
            var hop0 = rReconstructHopDag(aggInput, hopMemo)

            // AggUnaryOp always requires MATRIX input
            if( hop0.dataType == Expression.DataType.SCALAR ) {
                hop0 = HopRewriteUtils.createUnary(hop0, OpOp1.CAST_AS_MATRIX)
                if( LOG.isTraceEnabled )
                    LOG.trace("inserted cast_as_matrix id=${hop0.hopID} for input to AggUnaryOp")
            }

            // Determine direction
            SNodeException.check(agg.aggreateNames.size in 1..2, agg)
            {"don't know how to compile aggregate to Hop with aggregates ${agg.aggreateNames}"}
            var dir = when {
                agg.aggreateNames.size == 2 -> Hop.Direction.RowCol
                // change to RowCol when aggregating vectors, in order to create a scalar rather than a 1x1 matrix
                hop0.dim2 == 1L -> Hop.Direction.RowCol // sum first dimension ==> row vector : Hop.Direction.Col
                hop0.dim1 == 1L -> Hop.Direction.RowCol // sum second dimension ==> col vector: Hop.Direction.Row
                agg.aggreateNames[0] == aggInput.schema.names[0] -> {
                    agg.check(aggInput.schema.size == 2) {"this may be erroneous if aggInput is not a matrix: ${aggInput.id} $aggInput ${aggInput.schema}"}
                    Hop.Direction.Col
                }
                else -> {
                    agg.check(aggInput.schema.size == 2) {"this may be erroneous if aggInput is not a matrix: ${aggInput.id} $aggInput ${aggInput.schema}"}
                    Hop.Direction.Row
                }
            }

            // minindex, maxindex only defined on Row aggregation
            // In general it is difficult to tell whether the input should be tranposed or not. We do our best.
            if( agg.op == Hop.AggOp.MININDEX || agg.op == Hop.AggOp.MAXINDEX ) {
                if( dir == Hop.Direction.RowCol && hop0.classify() == HopClass.COL_VECTOR || dir == Hop.Direction.Col ) {
                    hop0 = HopRewriteUtils.createTranspose(hop0)
                    if( LOG.isDebugEnabled )
                        LOG.debug("Creating transpose on input to ${agg.op} hopid=${hop0.hopID}")
                }
                dir = Hop.Direction.Row
            }

            val ret = HopRewriteUtils.createAggUnaryOp(hop0, agg.op, dir)
            if( LOG.isTraceEnabled )
                LOG.trace("Decide direction $dir on input dims [${hop0.dim1},${hop0.dim2}], schema $aggInput, " +
                        "aggregating on ${agg.aggreateNames} by ${agg.op} to schema ${agg.schema} for SNode ${agg.id} and new Hop ${ret.hopID}")
            ret
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

    private fun reconstructNary(nary: SNodeNary, hopMemo: MutableMap<SNode, Hop>): Hop {
        val hopInputs = nary.inputs.mapTo(ArrayList()) { input ->
                rReconstructHopDag(input, hopMemo)
        }

        // if joining on two names and both matrices, ensure that they align by possibly transposing one of them
        if( nary.inputs.size == 2 && nary.inputs[0].schema.size == 2
                && nary.inputs[0].schema.names.toSet() == nary.inputs[1].schema.names.toSet() ) {
            if( nary.inputs[0].schema.names[0] != nary.inputs[1].schema.names[0] ) {
                hopInputs[1] = HopRewriteUtils.createTranspose(hopInputs[1])
                if( LOG.isDebugEnabled )
                    LOG.debug("transpose second matrix ${nary.inputs} hopid=${hopInputs[1].hopID} to match matrix element-wise multiply id=${nary.inputs[1].id}")
            }
        }

        // if joining on one name and both vectors, ensure that they align by possibly transposing one of them
        if( nary.inputs.size == 2 && nary.inputs[0].schema.size == 1 && nary.inputs[0].schema == nary.inputs[1].schema) {
            assert(hopInputs[0].classify().isVector)
            assert(hopInputs[1].classify().isVector)
            if( hopInputs[0].classify() != hopInputs[1].classify() ) {
                hopInputs[1] = HopRewriteUtils.createTranspose(hopInputs[1])
                if( LOG.isDebugEnabled )
                    LOG.debug("transpose vector ${nary.inputs[1]} id=${nary.inputs[1].id} hopid=${hopInputs[1].hopID} to match vector element-wise multiply")
            }
        }

        // matrix-vector element-wise multiply case (vector expansion)
        // swap inputs if matrix is on right
        // transpose vector if it does not match the correct dimension
        if( nary.inputs.size == 2 &&
                (nary.inputs[0].schema.size == 2 && nary.inputs[1].schema.size == 1 ||
                nary.inputs[1].schema.size == 2 && nary.inputs[0].schema.size == 1))
        {
            val (mat,vec) = if( nary.inputs[1].schema.size == 2 ) {
                hopInputs.swap(0,1)
                nary.inputs[1] to nary.inputs[0]
            } else
                nary.inputs[0] to nary.inputs[1]
            assert(hopInputs[1].classify().isVector)
            if( vec.schema.names[0] == mat.schema.names[0] ) {
                // require vector to be column
                if( hopInputs[1].classify() != HopClass.COL_VECTOR ) {
                    hopInputs[1] = HopRewriteUtils.createTranspose(hopInputs[1])
                    if( LOG.isDebugEnabled )
                        LOG.debug("transpose vector $vec to col vector to match vector expansion element-wise multiply on first dimension of matrix $mat")
                }
            } else if ( vec.schema.names[0] == mat.schema.names[1] ) {
                // require vector to be row
                if( hopInputs[1].classify() != HopClass.ROW_VECTOR ) {
                    hopInputs[1] = HopRewriteUtils.createTranspose(hopInputs[1])
                    if( LOG.isDebugEnabled )
                        LOG.debug("transpose vector $vec to row vector to match vector expansion element-wise multiply on second dimension of matrix $mat")
                }
            } else throw SNodeException(nary, "attribute name of vector does not match either attribute name of matrix in vector-expansion element-wise multiply")

        }


        // check for outer product: nary(*) between two vectors whose names do not join
        return if( nary.op == NaryOp.MULT && nary.inputs[0].schema.size == 1 && nary.inputs[1].schema.size == 1
                && nary.inputs[0].schema.names[0] != nary.inputs[1].schema.names[0] ) {
            HopRewriteUtils.createMatrixMultiply(hopInputs[0], hopInputs[1])
        }
        else
            when( nary.inputs.size ) {
                1 -> HopRewriteUtils.createUnary(hopInputs[0], OpOp1.valueOf(nary.op.name))
                2 -> HopRewriteUtils.createBinary(hopInputs[0], hopInputs[1], OpOp2.valueOf(nary.op.name))
                3 -> HopRewriteUtils.createTernary(hopInputs[0], hopInputs[1], hopInputs[2], OpOp3.valueOf(nary.op.name))
                else -> throw SNodeException(nary, "don't know how to reconstruct a Hop from an nary with ${nary.inputs.size} inputs $nary")
            }
    }



    // Later we will map blocks between bind/unbind all at once, into either Fused Ops or Regular Hops.
    private fun rReconstructHopDag(current: SNode, hopMemo: MutableMap<SNode, Hop>): Hop {
        if (current.visited) {
            return hopMemo[current]!!
        }

        val node: Hop = when( current ) {
            is SNodeData -> {
                //recursively process child nodes
                val inputs = current.inputs.mapTo(arrayListOf()) { rReconstructHopDag(it, hopMemo) }

                if( current.isWrite ) {
                    if (current.hop.dataType == Expression.DataType.SCALAR && inputs[0].dataType != Expression.DataType.SCALAR) {
                        if (LOG.isDebugEnabled)
                            LOG.debug("on $current id=${current.id}, casting input 0 to scalar in order to match previous Write DataOp ${current.hop} hopid=${current.hop.hopID}")
                        current.check(inputs[0].dim1 == 1L && inputs[0].dim2 == 1L) {"attempt to cast to scalar fails because dims are not 1,1 in inputs[0] ${inputs[0]} hopid=${inputs[0].hopID}"}
                        inputs[0] = HopRewriteUtils.createUnary(inputs[0], OpOp1.CAST_AS_SCALAR)
                    } else if (current.hop.dataType != Expression.DataType.SCALAR && inputs[0].dataType == Expression.DataType.SCALAR) {
                        current.check(inputs[0].dim1 == 0L && inputs[0].dim2 == 0L) {"attempt to cast to matrix fails because dims are not 0,0 in inputs[0] ${inputs[0]} hopid=${inputs[0].hopID}"}
                        if (LOG.isDebugEnabled)
                            LOG.debug("on $current id=${current.id}, casting input 0 to matrix in order to match previous Write DataOp ${current.hop} hopid=${current.hop.hopID}")
                        inputs[0] = HopRewriteUtils.createUnary(inputs[0], OpOp1.CAST_AS_MATRIX)
                    }
                }

                for( i in inputs.indices ) {
                    val oldHopClass = current.hop.input[i]!!.classify() //current.inputHopClasses[i]
                    if( oldHopClass.isVector ) {
                        if( inputs[i].classify() != oldHopClass ) {
                            inputs[i] = HopRewriteUtils.createTranspose(inputs[i])
                            if( LOG.isDebugEnabled )
                                LOG.debug("on $current id=${current.id}, created transpose to force orientation to $oldHopClass on input $i")
                        }
                    }
                }
                if (inputs.isNotEmpty()) {
                    HopRewriteUtils.replaceChildReference(current.hop,
                            current.hop.input[0], inputs[0], 0)
                }
                current.hop.parent.removeIf { it !is DataOp || it.input.indexOf(current.hop) == 0 }
                current.hop.resetVisitStatus() // visit status may be set from SNode construction
                current.hop.refreshSizeInformation()
                current.hop
            }
            is SNodeExt -> {
                val inputs = current.inputs.mapTo(arrayListOf()) { rReconstructHopDag(it, hopMemo) }
                current.hop.resetVisitStatus() // visit status may be set from SNode construction

                // prevent duplicate CAST_AS_SCALAR
//                if( current.hop is UnaryOp && current.hop.op == OpOp1.CAST_AS_SCALAR
//                        && inputs[0] is UnaryOp && (inputs[0] as UnaryOp).op == OpOp1.CAST_AS_SCALAR ) {
//                    inputs = inputs[0].input
//                    inputs[0].parent.clear()
//                }
                if( HopRewriteUtils.isUnary(current.hop, OpOp1.CAST_AS_SCALAR)
                        && inputs[0].dataType.isScalar ) {
                    // skip the cast
                    inputs[0]
                }
                else if( HopRewriteUtils.isUnary(current.hop, OpOp1.CAST_AS_MATRIX)
                        && inputs[0].dataType.isMatrix ) {
                    // skip the cast
                    inputs[0]
                }
                else {
                    // change input orientation if necessary
                    for( i in inputs.indices ) {
                        val oldHopClass = current.hop.input[i]!!.classify() //current.inputHopClasses[i]
                        if( oldHopClass.isVector ) {
                            if( inputs[i].classify() != oldHopClass ) {
                                inputs[i] = HopRewriteUtils.createTranspose(inputs[i])
                                if( LOG.isTraceEnabled )
                                    LOG.trace("on $current id=${current.id}, created transpose to force orientation to $oldHopClass on input $i of $current")
                            }
                        }
                    }

                    if (inputs.isNotEmpty()) { //robustness datagen
                        HopRewriteUtils.removeAllChildReferences(current.hop)
                        for (c in inputs)
                            current.hop.addInput(c)
                    }
                    current.hop.parent.removeIf { it !is DataOp || it.input.indexOf(current.hop) == 0 }
                    current.hop
                }
            }
            is SNodeAggregate -> reconstructAggregate(current, hopMemo)
            is SNodeNary -> reconstructNary(current, hopMemo)
            is SNodeUnbind -> {
                // match on the SNode beneath SNodeUnbind. Go to the Binds that are children to this block.
                val bu = current.inputs[0]
                val hop = when( bu ) {
                    is SNodeAggregate -> reconstructAggregate(bu, hopMemo)
                    is SNodeNary -> reconstructNary(bu, hopMemo)
                    is SNodeBind -> { // unbind-bind
                        rReconstructHopDag(bu.inputs[0], hopMemo)
                    }
                    else -> throw SNodeException("don't know how to translate (${bu.id}) $bu")
                }
                // check if the Unbind necessitates a permutation
                // if the Unbind has a map of Int to Attribute that does not agree with the schema of the input, then transpose
                if( current.unbindings.any { (pos,n) -> current.input.schema.names[pos] != n } ) {
                    // log this in case we encounter transpose issues
                    if( LOG.isDebugEnabled )
                        LOG.debug("insert transpose at Unbind (${current.id}) $current with input (${current.input.id}) ${current.input} ${current.input.schema}")
                    HopRewriteUtils.createTranspose(hop)
                }
                else
                    hop
            }
            is SNodeBind -> {
                // ignore SNodeBind
                rReconstructHopDag(current.inputs[0], hopMemo)
            }
            else -> throw SNodeException(current, "recurse on unknown SNode")
        }

        current.visited = true
        hopMemo.put(current, node)

        return node
    }
}
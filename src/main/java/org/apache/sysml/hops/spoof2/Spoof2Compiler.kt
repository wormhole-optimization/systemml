package org.apache.sysml.hops.spoof2

import com.google.common.collect.ArrayListMultimap
import com.google.common.collect.ListMultimap
import org.apache.commons.logging.LogFactory
import org.apache.log4j.Level
import org.apache.log4j.Logger
import org.apache.sysml.hops.*
import org.apache.sysml.hops.Hop.*
import org.apache.sysml.hops.rewrite.*
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.plan.SNodeNary.NaryOp
import org.apache.sysml.hops.spoof2.rewrite.SPlanNormalFormRewriter
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriter
import org.apache.sysml.parser.*
import org.apache.sysml.runtime.DMLRuntimeException
import org.apache.sysml.utils.Explain
import java.util.*

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
        for (i in 0 until dmlprog.numStatementBlocks) {
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
        rewriter2.rewriteHopDAG(roots, ProgramRewriteStatus())
        Hop.resetVisitStatus(roots)
        return roots
    }

    // dim -> <Input -> Dim>
    private fun dimsToInputDims(root: SNode): List<ListMultimap<SNode, AU>> {
        return root.schema.map { (n,_) ->
            val mm = ArrayListMultimap.create<SNode, AU>()
            when( n ) {
                is AB -> mapToInputs(root, n, mm)
                is AU -> mapToInputs(root, n, mm)
            }
            mm
        }
    }

    private fun mapToInputs(node: SNode, i: AU, mm: ListMultimap<SNode, AU>) {
        when( node ) {
            is SNodeData -> {
                if( node.isWrite ) mapToInputs(node.inputs[0], i, mm)
                else if( node.isLiteral )
                else mm.put(node, i)
            }
            is SNodeBind -> mapToInputs(node.input, i, mm)
            is SNodeUnbind -> {
                if( node.unbindings.containsKey(i) )
                    mapToInputs(node.input, node.unbindings[i]!!, mm)
                else
                    mapToInputs(node.input, i, mm)
            }
            is SNodeExt -> mm.put(node, i)
            else -> throw SNodeException(node, "don't know how to handle snode type $node")
        }
    }
    private fun mapToInputs(node: SNode, n: AB, mm: ListMultimap<SNode, AU>) {
        when( node ) {
            is SNodeBind -> {
                if( n in node.bindings.values )
                    mapToInputs(node.input, node.bindings.entries.find { it.value == n }!!.key, mm)
                else
                    mapToInputs(node.input, n, mm)
            }
            else -> node.inputs.filter { n in it.schema }.map { mapToInputs(it, n, mm) }
        }
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

        ProgramRewriter(RewriteCommonSubexpressionElimination()).rewriteHopDAG(roots, ProgramRewriteStatus())

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

        // for each root, a map from input dimensions (acutally a list) to the base inputs and input dimensions
        val baseInputs = sroots.map { sroot ->
            dimsToInputDims(sroot)
        }
        // strip all transposes


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
        val hopMemo: MutableMap<SNode, Pair<Hop, Map<AU,AB>>> = hashMapOf()
        for (sroot in sroots) {
            val (h,_) = rReconstructHopDag(sroot, hopMemo)
            roots2.add(h)
        }

        val baseInputs2 = sroots.map { sroot ->
            dimsToInputDims(sroot)
        }
        if( LOG.isTraceEnabled ) {
            LOG.trace("Base input map: ${baseInputs.mapIndexed {i, bil -> "\nr$i\t${bil.mapIndexed { d, bi -> "d$d: $bi" }.joinToString("\n\t")}"}.reduce(String::plus)}" +
                    "\nBase input map2: ${baseInputs2.mapIndexed {i, bil -> "\nr$i\t${bil.mapIndexed { d, bi -> "d$d: $bi" }.joinToString("\n\t")}"}.reduce(String::plus)}")
        }


        // add transposes if necessary to roots in order to maintain same orientation as original
        // shouldn't be necessary because the roots are generally Writes, which correct orientation on their own
        roots2.mapInPlaceIndexed { idx, root2 ->
            if( rootClasses[idx].isVector && root2.classify() != rootClasses[idx] ) {
                check( root2.classify().isVector ) {"root changed type after reconstruction? Old type ${rootClasses[idx]}; new type ${root2.classify()} dims ${root2.dim1}, ${root2.dim2} hopid=${root2.hopID}" +
                        "\n modified Hop Dag is:\n" + Explain.explainHops(roots2)}
                if( LOG.isTraceEnabled )
                    LOG.trace("creating root transpose at root $idx to enforce orientation ${rootClasses[idx]}")
                transposeRoot(root2)
            } else if( rootClasses[idx] == HopClass.MATRIX ) { // check data flow
                val bi = baseInputs[idx]
                // does dim 0 base inputs == dim 1 base inputs? If so, it is symmetric and orientation does not matter.
                if( bi[0] == bi[1] )
                    root2
                else {
                    val bi2 = baseInputs2[idx]
                    // Does bi[0] and bi[1] have different unique inputs? If so, distinguish based on # of unique inputs.
                    val biu = bi.map { it.asMap().mapValues { (_,v) -> v.distinct() }.toList().distinct() }
                    if( biu[0] != biu[1] ) {
                        val biu2 = bi2.map { it.asMap().mapValues { (_,v) -> v.distinct() }.toList().distinct() }
                        when {
                            biu[0] == biu2[0] -> // need better method?
                                root2
                            biu[0] == biu2[1] -> {
                                if( LOG.isTraceEnabled )
                                    LOG.trace("create root transpose at root $idx based on data flow; unique inputs differ case")
                                transposeRoot(root2)
                            }
                            biu[0].toSet() == biu2[0].toSet() -> root2
                            biu[0].toSet() == biu2[1].toSet() -> {
                                if( LOG.isTraceEnabled )
                                    LOG.trace("create root transpose at root $idx based on data flow; unique inputs differ case (by set)")
                                transposeRoot(root2)
                            }
                            else -> throw SNodeException(sroots[idx], "Failed to distinguish orientation for old Hop root ${roots[idx].hopID} and new Hop root ${root2.hopID}; " +
                                    "baseInputs have different unique inputs but neither equal to base inputs 2:" +
                                    "\n\t0: ${biu[0].map { (k,_) -> k }.toSet().joinToString { "(${it.id})$it" }}" +
                                    "\n\t1: ${biu[1].map { (k,_) -> k }.toSet().joinToString { "(${it.id})$it" }}" +
                                    "\n\t0: ${biu2[0].map { (k,_) -> k }.toSet().joinToString { "(${it.id})$it" }}" +
                                    "\n\t1: ${biu2[0].map { (k,_) -> k }.toSet().joinToString { "(${it.id})$it" }}")
                        }
                    } else {
                        // for each unique base input, if the number of base inputs is different between dimensions,
                        // go with the orientation that agrees with the disparity
                        @Suppress("NAME_SHADOWING")
                        val r = bi[0].keySet().fold(-1) { commit, uniqueBase ->
                            // bi[0] is the base input of root dimension 0
                            // x1[0] corresponds to bi[0]
                            // x1[0][0] is the first dimension of the base input
                            val x1 = bi.map { it[uniqueBase]!!.groupBy { it }.map { it.key to it.value.count() }.sortedBy { it.first }.map { it.second }}
                            val x2 = bi2.map { it[uniqueBase]!!.groupBy { it }.map { it.key to it.value.count() }.sortedBy { it.first }.map { it.second }}
                            // -1 -> uncommitted; 0 -> commit no transpose; 1 -> commit transpose
                            x1[0].indices.fold(commit) { commit, baseIdx ->
                                val c = x1[0][baseIdx].compareTo(x1[1][baseIdx])
                                if( c == 0 )
                                    commit
                                else {
                                    val c2 = x2[0][baseIdx].compareTo(x2[1][baseIdx])
                                    val newCommit = when (c2) {
                                        0 -> commit
                                        c -> 0
                                        else -> 1
                                    }
                                    if( commit >= 0 && commit != newCommit )
                                        throw SNodeException(sroots[idx], "Failed to distinguish orientation for old Hop root ${roots[idx].hopID} and new Hop root ${root2.hopID}; " +
                                                "baseInputs have same unique inputs and on input $uniqueBase, diagreeement with a previous unique input")
                                    newCommit
                                }
                            }
                        }
                        when( r ) {
                            0 -> root2
                            1 -> {
                                if( LOG.isTraceEnabled )
                                    LOG.trace("create root transpose at root $idx based on data flow; unique inputs equal case")
                                transposeRoot(root2)
                            }
                            -1 -> root2 // symmetric again
                            else -> throw AssertionError("impossible by design")
                        }
                    }
                }
            } else // scalar or ok vector
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
        ProgramRewriter(RewriteCommonSubexpressionElimination()).rewriteHopDAG(roots, ProgramRewriteStatus())
        programRewriteHops(roots2, recompile, doDynamicProgramRewriter)
//        if( doDynamicProgramRewriter )
//            RewriteAlgebraicSimplificationDynamic().rewriteHopDAGs(roots2, ProgramRewriteStatus())

        HopDagValidator.validateHopDag(roots2)

        if (LOG.isTraceEnabled) {
            LOG.trace("Spoof2Compiler rewritten modified HOP DAG: \n" + Explain.explainHops(roots2))
        }

        return roots2
    }

    private fun transposeRoot(root2: Hop): Hop {
        return if( root2 is DataOp && root2.isWrite ) {
            val child = root2.input[0]
            child.parent -= root2
            root2.input[0] = HopRewriteUtils.createTranspose(child)
            root2.input[0].parent += root2
            root2.refreshSizeInformation()
            root2
        } else
            HopRewriteUtils.createTranspose(root2)
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

                        val flipBindings = mapOf(AU.U0 to bindings[AU.U1]!!, AU.U1 to bindings[AU.U0]!!)
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

                    val boundNames = mutableMapOf<AU,AB>()
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
                        SNodeAggregate(current.op, inputs[0], bs[AU.U0]!!)
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
                if( current.innerOp.name in NaryOp ) {
                    val boundNames = mutableMapOf<AU,AB>()
                    val aggName: AB?
                    when (current.input[0].classify()) {
                        HopClass.SCALAR -> throw HopsException("AggBinaryOp id=${current.hopID} should not act on scalars but input SNodes are $inputs")
                        HopClass.COL_VECTOR -> {
                            HopsException.check(current.input[1].classify() == HopClass.ROW_VECTOR
                                    || current.input[1].classify() == HopClass.SCALAR, current,
                                    "Column vector on left must multiply with row vector on right")
                            // outer product
                            val bs0 = inputs[0].schema.genAllBindings()
                            inputs[0] = SNodeBind(inputs[0], bs0)
                            boundNames += AU.U0 to bs0[AU.U0]!!
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
                            aggName = bs0[AU(inputs[0].schema.size - 1)]!!
                            val bs1 = mutableMapOf(AU.U0 to aggName)
                            inputs[1].schema.fillWithBindings(bs1) // match row vector binding with first dim on inputs[1]
                            inputs[1] = SNodeBind(inputs[1], bs1)
                            if( inputs[0].schema.size == 2 ) boundNames += AU.U0 to bs0[AU.U0]!!
                            if( inputs[1].schema.size == 2 ) boundNames += AU(boundNames.size) to bs1[AU.U1]!!
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


    private fun reconstructAggregate(agg: SNodeAggregate, hopMemo: MutableMap<SNode, Pair<Hop, Map<AU,AB>>>): Pair<Hop, Map<AU,AB>> {
        val mult = agg.input

        return if( mult is SNodeNary && mult.op == NaryOp.MULT && agg.op == Hop.AggOp.SUM
                && mult.inputs.size == 2
                && mult.inputs[0].schema.names.intersect(mult.inputs[1].schema.names).size == 1 // forbear element-wise multiplication followed by agg
                && agg.aggs.size == 1 )
        {   // MxM
            var mult0 = mult.inputs[0]
            var mult1 = mult.inputs[1]

            // We may have a Bind because the output is a scalar (thus no Unbind)
            // but the inputs are non-scalars (and are therefore Bound)
            var (hop0, mapInput0) = rReconstructHopDag(mult0, hopMemo).let { it.first to it.second.toMutableMap() }
            var (hop1, mapInput1) = rReconstructHopDag(mult1, hopMemo).let { it.first to it.second.toMutableMap() }

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
            if( mapInput0.size == 2 && mapInput1.size == 1 ) {
                val tmp = mult0; mult0 = mult1; mult1 = tmp
                val t = hop0; hop0 = hop1; hop1 = t
                val tt = mapInput0; mapInput0 = mapInput1; mapInput1 = tt
            }
            // check positions of labels and see if we need to transpose
            val aggName: Name = agg.aggs.names.first()
            val fm: MutableMap<AU,AB> = mutableMapOf()
            when( mapInput0.size ) {
                1 -> when( mapInput1.size ) { // hop0 is V
                    1 -> when( hop0.classify() ) { // hop1 is V; inner product
                        HopClass.ROW_VECTOR -> when( hop1.classify() ) {
                            HopClass.COL_VECTOR -> {}
                            HopClass.ROW_VECTOR -> {hop1 = HopRewriteUtils.createTranspose(hop1)} //; swap01(mapInput1)}
                            else -> throw AssertionError()
                        }
                        HopClass.COL_VECTOR -> when( hop1.classify() ) {
                            HopClass.COL_VECTOR -> {hop0 = HopRewriteUtils.createTranspose(hop0)} //; swap01(mapInput0)}
                            HopClass.ROW_VECTOR -> {val t = hop0; hop0 = hop1; hop1 = t; val tt = mapInput0; mapInput0 = mapInput1; mapInput1 = tt}
                            else -> throw AssertionError()
                        }
                        else -> throw AssertionError()
                    }
                    2 -> { // hop1 is M; check VxM or MxV
                        // get matching name, which is also aggregated over
                        fm.put(AU.U0, mapInput1.entries.find { (_,ab) -> ab != aggName }!!.value)
                        val i1 = mapInput1.invert()[aggName]; agg.check(i1 != null) {"$mult1 should have the name $aggName we are aggregating over"}
                        when( i1!!.dim ) {
                            0 -> when( hop0.classify() ) { // VxM; ensure vector is a row vector
                                HopClass.ROW_VECTOR -> {}
                                HopClass.COL_VECTOR -> {hop0 = HopRewriteUtils.createTranspose(hop0)} //; swap01(mapInput0)}
                                else -> throw AssertionError()
                            }
                            1 -> { // MxV; swap hops and ensure vector is a col vector
                                val t = hop0; hop0 = hop1; hop1 = t
                                val tt = mapInput0; mapInput0 = mapInput1; mapInput1 = tt
                                when( hop1.classify() ) {
                                    HopClass.ROW_VECTOR -> {hop1 = HopRewriteUtils.createTranspose(hop1)} //; swap01(mapInput1)}
                                    HopClass.COL_VECTOR -> {}
                                    else -> throw AssertionError()
                                }
                            }
                        }
                    }
                }
                2 -> { // MxM case
                    val i0 = mapInput0.invert()[aggName]; agg.check(i0 != null) {"$mult0 should have the name $aggName we are aggregating over"}
                    val i1 = mapInput1.invert()[aggName]; agg.check(i1 != null) {"$mult1 should have the name $aggName we are aggregating over"}
                    // make common attribute on position 1 of hop0 and position0 of hop1
                    when( i0!!.dim ) {
                        0 -> when( i1!!.dim ) {
                            0 -> {hop0 = HopRewriteUtils.createTranspose(hop0); swap01(mapInput0)}       //[b,a]x[b,c]
                            1 -> { val tmp = hop0; hop0 = hop1; hop1 = tmp     //[b,a]x[c,b]
                                val tt = mapInput0; mapInput0 = mapInput1; mapInput1 = tt
                                // also switch the SNode plan inputs and refresh schema, for later reconstruction
                                if( LOG.isTraceEnabled )
                                    LOG.trace("Switch MxM inputs of (${mult.id}) $mult ${mult.schema}")
                                mult.inputs.reverse()
                                mult.refreshSchemasUpward() // refresh schema of all parents above, as long as schema changes
                            }
                        }
                        1 -> when( i1!!.dim ) {
                            0 -> {}                                                 //[a,b]x[b,c]
                            1 -> {hop1 = HopRewriteUtils.createTranspose(hop1); swap01(mapInput1)}       //[a,b]x[c,b]
                        }
                    }
                    fm.put(AU.U0, mapInput0[AU.U0]!!)
                    fm.put(AU.U1, mapInput1[AU.U1]!!)
                }
            }
            var mxm: Hop = HopRewriteUtils.createMatrixMultiply(hop0, hop1)
            if( mxm.dim1 == 1L && mxm.dim2 == 1L ) {
                if( LOG.isDebugEnabled )
                    LOG.debug("Casting result of matrix multiply ${mxm.hopID} to scalar")
                mxm = HopRewriteUtils.createUnary(mxm, OpOp1.CAST_AS_SCALAR)
            }
            mxm to fm
        }
        else { // general Agg

            // if aggInput does not have an aggName in its schema, then the aggregation is constant over that attribute.
            // see Spoof2Test#44 sum(A+7) --> sum(A) + 7*nrow(A)*ncol(A)
            val constantAggs = agg.aggsNotInInputSchema()
            if( constantAggs.isNotEmpty() ) {
                when( agg.op ) {
                    Hop.AggOp.MIN, Hop.AggOp.MAX, Hop.AggOp.MEAN -> {}
                    Hop.AggOp.SUM -> {
                        val mFactor = constantAggs.shapes.fold(1L, Long::times)
                        val lit = SNodeData(LiteralOp(mFactor))

                        agg.input.parents -= agg
                        val newInput = SNodeNary(NaryOp.MULT, agg.input, lit)
                        newInput.parents += agg
                        agg.input = newInput

                        agg.aggs -= constantAggs
                    }
                    else -> throw UnsupportedOperationException("don't know how to handle constant aggregation with on $agg over constant attributes $constantAggs")
                }
            }

            val aggInput = agg.input
            var (hop0, mi) = rReconstructHopDag(aggInput, hopMemo)
            if( agg.aggs.isEmpty() ) // empty aggregation
                return hop0 to mi

            // AggUnaryOp always requires MATRIX input
            if( hop0.dataType == Expression.DataType.SCALAR ) {
                hop0 = HopRewriteUtils.createUnary(hop0, OpOp1.CAST_AS_MATRIX)
                if( LOG.isTraceEnabled )
                    LOG.trace("inserted cast_as_matrix id=${hop0.hopID} for input to AggUnaryOp")
            }

            // Determine direction
            SNodeException.check(agg.aggs.size in 1..2, agg)
            {"don't know how to compile aggregate to Hop with aggregates ${agg.aggs}"}
            var dir = when {
                agg.aggs.size == 2 -> Hop.Direction.RowCol
            // change to RowCol when aggregating vectors, in order to create a scalar rather than a 1x1 matrix
                hop0.dim2 == 1L -> Hop.Direction.RowCol // sum first dimension ==> row vector : Hop.Direction.Col
                hop0.dim1 == 1L -> Hop.Direction.RowCol // sum second dimension ==> col vector: Hop.Direction.Row
                agg.aggs.names.first() == mi[AU.U0]!! -> {
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
                        "aggregating on ${agg.aggs} by ${agg.op} to schema ${agg.schema} for SNode ${agg.id} and new Hop ${ret.hopID}")
            mi = if( agg.schema.isNotEmpty() ) {
                agg.check(agg.schema.size == 1) {"expect agg to have 0 or 1 attributes in schema: ${agg.id} $agg ${agg.schema}"}
                mapOf(AU.U0 to agg.schema.names.first() as AB)
            }  else mapOf()
            ret to mi
        }
    }

//    // cast matrix to scalar
//    // sometimes this is necessary, sometimes not
//    // code in the SNodeExt reconstruct to Hop block checks for duplicate CAST_AS_SCALAR
//    private fun checkCastScalar(hop: Hop): Hop {
//        return if( hop.dimsKnown() && hop.dim1 == 1L && hop.dim2 == 1L && hop.dataType == Expression.DataType.MATRIX )
//            HopRewriteUtils.createUnary(hop, OpOp1.CAST_AS_SCALAR)
//        else
//            hop
//    }

    private fun reconstructNary(nary: SNodeNary, hopMemo: MutableMap<SNode, Pair<Hop, Map<AU,AB>>>): Pair<Hop, Map<AU,AB>> {
        val (hopInputs, mis) = nary.inputs.map { input ->
            rReconstructHopDag(input, hopMemo)
        }.unzip().let { it.first.toMutableList() to it.second.toMutableList() }

        when( nary.op ) {
            NaryOp.MULT, NaryOp.PLUS ->
                    if(hopInputs.size == 1)
                        return hopInputs[0] to mis[0]
            else -> {}
        }

        if( nary.inputs.size == 2 ) {
            // if joining on two names and both matrices, ensure that they align by possibly transposing one of them
            if (nary.inputs[0].schema.size == 2 && nary.inputs[1].schema.size == 2) {
                if (mis[0][AU.U0]!! != mis[1][AU.U0]!!) {
                    hopInputs[1] = HopRewriteUtils.createTranspose(hopInputs[1])
                    if (LOG.isDebugEnabled)
                        LOG.debug("transpose second matrix ${nary.inputs} hopid=${hopInputs[1].hopID} to match matrix element-wise multiply id=${nary.inputs[1].id}")
                }
            }
            // if joining on one name and both vectors, ensure that they align by possibly transposing one of them
            else if (nary.inputs[0].schema.size == 1 && nary.inputs[0].schema == nary.inputs[1].schema) {
                assert(hopInputs[0].classify().isVector)
                assert(hopInputs[1].classify().isVector)
                if (hopInputs[0].classify() != hopInputs[1].classify()) {
                    hopInputs[1] = HopRewriteUtils.createTranspose(hopInputs[1])
                    if (LOG.isDebugEnabled)
                        LOG.debug("transpose vector ${nary.inputs[1]} id=${nary.inputs[1].id} hopid=${hopInputs[1].hopID} to match vector element-wise multiply")
                }
            }
            // matrix-vector element-wise multiply case (vector expansion)
            // swap inputs if matrix is on right
            // transpose vector if it does not match the correct dimension
            else if (nary.inputs[0].schema.size == 2 && nary.inputs[1].schema.size == 1 ||
                            nary.inputs[1].schema.size == 2 && nary.inputs[0].schema.size == 1) {
                val (mat, vec) = if (nary.inputs[1].schema.size == 2) {
                    hopInputs.swap(0, 1)
                    mis[0] = mis[1]
                    nary.inputs[1] to nary.inputs[0]
                } else
                    nary.inputs[0] to nary.inputs[1]
                assert(hopInputs[1].classify().isVector)
                val vec1 = vec.schema.names.first()
                val (mat1, mat2) = mis[0][AU.U0]!! to mis[0][AU.U1]!! //mat.schema.names.firstSecond()
                if (vec1 == mat1) {
                    // require vector to be column
                    if (hopInputs[1].classify() != HopClass.COL_VECTOR) {
                        hopInputs[1] = HopRewriteUtils.createTranspose(hopInputs[1])
                        if (LOG.isDebugEnabled)
                            LOG.debug("transpose vector $vec to col vector to match vector expansion element-wise multiply on first dimension of matrix $mat")
                    }
                } else if (vec1 == mat2) {
                    // require vector to be row
                    if (hopInputs[1].classify() != HopClass.ROW_VECTOR) {
                        hopInputs[1] = HopRewriteUtils.createTranspose(hopInputs[1])
                        if (LOG.isDebugEnabled)
                            LOG.debug("transpose vector $vec to row vector to match vector expansion element-wise multiply on second dimension of matrix $mat")
                    }
                } else throw SNodeException(nary, "attribute name of vector does not match either attribute name of matrix in vector-expansion element-wise multiply")
            }
        }

        // check for outer product: nary(*) between two vectors whose names do not join
        return if( nary.op == NaryOp.MULT && nary.inputs[0].schema.size == 1 && nary.inputs[1].schema.size == 1
                && nary.inputs[0].schema.names.first() != nary.inputs[1].schema.names.first() ) {
            when( hopInputs[0].classify() ) {
                HopClass.ROW_VECTOR -> {
                    if( hopInputs[1].classify() == HopClass.ROW_VECTOR ) {
                        if( LOG.isTraceEnabled )
                            LOG.trace("transposing 2nd input (${hopInputs[1].hopID}) to outer product (${nary.id}) $nary ${nary.schema} - both are ROW; transpose second and swap")
                        hopInputs[1] = HopRewriteUtils.createTranspose(hopInputs[1])
                    }
                    nary.check(hopInputs[1].classify() == HopClass.COL_VECTOR) {"expected outer product but is not: $hopInputs with dims ${hopInputs.map { it.dim1 to it.dim2 }}"}
                    hopInputs.swap(0,1)
                    nary.inputs.swap(0,1)
                }
                HopClass.COL_VECTOR -> {
                    if( hopInputs[1].classify() == HopClass.COL_VECTOR ) {
                        if( LOG.isTraceEnabled )
                            LOG.trace("transposing 2nd input (${hopInputs[1].hopID}) to outer product (${nary.id}) $nary ${nary.schema} - both are COL; transpose second")
                        hopInputs[1] = HopRewriteUtils.createTranspose(hopInputs[1])
                    }
                    nary.check(hopInputs[1].classify() == HopClass.ROW_VECTOR){"expected outer product but is not: $hopInputs with dims ${hopInputs.map { it.dim1 to it.dim2 }}"}
                }
                else -> throw SNodeException(nary, "expected outer product but is not: $hopInputs with dims ${hopInputs.map { it.dim1 to it.dim2 }}")
            }
            HopRewriteUtils.createMatrixMultiply(hopInputs[0], hopInputs[1]) to
                    mapOf(AU.U0 to (nary.inputs[0].schema.names.first() as AB), AU.U1 to (nary.inputs[1].schema.names.first() as AB))
        }
        else
            when( nary.inputs.size ) {
                1 -> HopRewriteUtils.createUnary(hopInputs[0], OpOp1.valueOf(nary.op.name)) to mis[0]
                2 -> HopRewriteUtils.createBinary(hopInputs[0], hopInputs[1], OpOp2.valueOf(nary.op.name)) to if(mis[0].size >= mis[1].size) mis[0] else mis[1]
                3 -> HopRewriteUtils.createTernary(hopInputs[0], hopInputs[1], hopInputs[2], OpOp3.valueOf(nary.op.name)) to mis[0] // ?
                else -> throw SNodeException(nary, "don't know how to reconstruct a Hop from an nary with ${nary.inputs.size} inputs $nary")
            }
    }



    // Later we will map blocks between bind/unbind all at once, into either Fused Ops or Regular Hops.
    private fun rReconstructHopDag(current: SNode, hopMemo: MutableMap<SNode, Pair<Hop, Map<AU, AB>>>): Pair<Hop, Map<AU,AB>> {
        if (current.visited) {
            return hopMemo[current]!!
        }

        val node: Pair<Hop, Map<AU,AB>> = when( current ) {
            is SNodeData -> {
                //recursively process child nodes
                val inputs = current.inputs.mapTo(arrayListOf()) { rReconstructHopDag(it, hopMemo).first }

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
                    HopRewriteUtils.replaceChildReference(current.hop, current.hop.input[0], inputs[0], 0)
                }
                current.hop.parent.removeIf { it !is DataOp || it.input.indexOf(current.hop) == 0 }
                current.hop.resetVisitStatus() // visit status may be set from SNode construction
                current.hop.refreshSizeInformation()
                current.hop to mapOf()
            }
            is SNodeExt -> {
                val inputs = current.inputs.mapTo(arrayListOf()) { rReconstructHopDag(it, hopMemo).first }
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
                    inputs[0] to mapOf()
                }
                else if( HopRewriteUtils.isUnary(current.hop, OpOp1.CAST_AS_MATRIX)
                        && inputs[0].dataType.isMatrix ) {
                    // skip the cast
                    inputs[0] to mapOf()
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
                    current.hop to mapOf()
                }
            }
            is SNodeAggregate -> reconstructAggregate(current, hopMemo)
            is SNodeNary -> reconstructNary(current, hopMemo)
            is SNodeUnbind -> {
                // match on the SNode beneath SNodeUnbind. Go to the Binds that are children to this block.
                val bu = current.inputs[0]
                val (hop: Hop, inputMap: Map<AU,AB>) = when( bu ) {
                    is SNodeAggregate -> reconstructAggregate(bu, hopMemo)
                    is SNodeNary -> reconstructNary(bu, hopMemo)
                    is SNodeBind -> { // unbind-bind
                        rReconstructHopDag(bu.inputs[0], hopMemo).let { (h,m) -> h to (m + bu.bindings) }
                    }
                    else -> throw SNodeException("don't know how to translate (${bu.id}) $bu")
                }.let { it.first to it.second.toMutableMap() }
                if( inputMap.entries.intersect(current.unbindings.entries).size != current.unbindings.entries.size ) {
                    if( LOG.isTraceEnabled )
                        LOG.trace("insert transpose at unbind (${current.id}) $current")
                    HopRewriteUtils.createTranspose(hop) to (swap01(inputMap) - current.unbindings.keys)
                } else hop to (inputMap - current.unbindings.keys)
//                // check if the Unbind necessitates a permutation
//                // if the Unbind has a map of Int to Attribute that does not agree with the schema of the input, then transpose
//                if( current.unbindings.any { (pos,n) -> current.input.schema.names[pos] != n } ) {
//                    // log this in case we encounter transpose issues
//                    if( LOG.isDebugEnabled )
//                        LOG.debug("insert transpose at Unbind (${current.id}) $current with input (${current.input.id}) ${current.input} ${current.input.schema}")
//                    HopRewriteUtils.createTranspose(hop)
//                }
//                else
//                    hop
            }
            is SNodeBind -> {
                // ignore SNodeBind
                rReconstructHopDag(current.inputs[0], hopMemo).let { (h,m) -> h to (m + current.bindings) }
            }
            else -> throw SNodeException(current, "recurse on unknown SNode")
        }

        current.visited = true
        hopMemo.put(current, node)

        return node
    }

    private fun swap01(m: MutableMap<AU,AB>): MutableMap<AU,AB> {
        if( AU.U0 in m ) {
            if( AU.U1 in m ) {
                val z = m[AU.U0]!!
                m[AU.U0] = m[AU.U1]!!
                m[AU.U1] = z
            } else {
                m[AU.U1] = m.remove(AU.U0)!!
            }
        } else if( AU.U1 in m ) {
            m[AU.U0] = m.remove(AU.U1)!!
        }
        return m
    }

}
package org.apache.sysml.hops.spoof2

import com.google.common.collect.ArrayListMultimap
import com.google.common.collect.ListMultimap
import org.apache.commons.logging.LogFactory
import org.apache.log4j.Level
import org.apache.log4j.Logger
import org.apache.sysml.conf.DMLConfig
import org.apache.sysml.hops.*
import org.apache.sysml.hops.rewrite.*
import org.apache.sysml.hops.spoof2.enu.NormalFormExploreEq
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriteRule
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriter
import org.apache.sysml.parser.*
import org.apache.sysml.runtime.DMLRuntimeException
import org.apache.sysml.utils.Explain
import java.util.*

object Spoof2Compiler {
    internal val LOG = LogFactory.getLog(Spoof2Compiler::class.java.name)

    //internal configuration flags
    private const val LDEBUG = DMLConfig.SPOOF_DEBUG
    init {
        if (LDEBUG) Logger.getLogger("org.apache.sysml.hops.spoof2").level = Level.TRACE
    }

    // todo inefficient; might be fine just to check the top-level sizes
    fun allKnownSizes(hop: Hop): Boolean {
        if (!hop.dimsKnown())
            return false
        return hop.input.all { allKnownSizes(it) }
    }
    fun allKnownSizesAndNoPermuteMultiply(hop: Hop): Boolean {
        if (!hop.dimsKnown() || hop is AggBinaryOp && hop.hasLeftPMInput())
            return false
        return hop.input.all { allKnownSizesAndNoPermuteMultiply(it) }
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
        rewriter2.rewriteHopDAG(roots, ProgramRewriteStatus())
        Hop.resetVisitStatus(roots)
        return roots
    }

    // dim -> <Input -> Dim>
    private fun dimsToInputDims(root: SNode): List<ListMultimap<Hop, AU>> {
        return root.schema.map { (n,_) ->
            val mm = ArrayListMultimap.create<Hop, AU>()
            when( n ) {
                is AB -> mapToInputs(root, n, mm)
                is AU -> mapToInputs(root, n, mm)
            }
            mm
        }
    }

    private fun mapToInputs(node: SNode, i: AU, mm: ListMultimap<Hop, AU>) {
        when( node ) {
            is SNodeData -> {
                if( node.isWrite ) mapToInputs(node.inputs[0], i, mm)
                else if( node.isLiteral )
                else mm.put(node.hop, i)
            }
            is SNodeBind -> mapToInputs(node.input, i, mm)
            is SNodeUnbind -> {
                if( node.unbindings.containsKey(i) )
                    mapToInputs(node.input, node.unbindings[i]!!, mm)
                else
                    mapToInputs(node.input, i, mm)
            }
            is SNodeExt -> mm.put(node.hop, i)
            else -> throw SNodeException(node, "don't know how to handle snode type $node")
        }
    }
    private fun mapToInputs(node: SNode, n: AB, mm: ListMultimap<Hop, AU>) {
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
        if( roots.any { !allKnownSizesAndNoPermuteMultiply(it)} ) {
            if (LOG.isTraceEnabled)
                LOG.trace("Skipping Spoof2 due to unknown sizes or a permutation MxM")
            return programRewriteHops(roots, recompile, doDynamicProgramRewriter)
        }

        ProgramRewriter(RewriteCommonSubexpressionElimination()).rewriteHopDAG(roots, ProgramRewriteStatus())

        if (LOG.isTraceEnabled)
            LOG.trace("Spoof2Compiler called for HOP DAG${if(recompile) " at RECOMPILE" else ""}: \n" + Explain.explainHops(roots))

        // remember top-level orientations
        val rootClasses = roots.map(Hop::classify)

        HopDagValidator.validateHopDag(roots)

        //construct sum-product plan
        var sroots = Hop2SPlan.hop2SPlan(roots)

        // if this is entirely composed of Data and Ext ops, then don't do Spoof2 because nothing to do
        if( sroots.all { it.isEntirelyDataExtEquals() } ) {
            if (LOG.isTraceEnabled) {
                LOG.trace("Skipping Spoof2 on DAG that is entirely composed of Data, Ext, and == nodes")
            }
            return programRewriteHops(roots, recompile, doDynamicProgramRewriter)
        }

        // for each root, a map from input dimensions (actually a list) to the base inputs and input dimensions
        val baseInputs = sroots.map { sroot -> dimsToInputDims(sroot) }

//        if (LOG.isTraceEnabled)
//            LOG.trace("Explain after initial SPlan construction: " + Explain.explainSPlan(sroots))

        val result2NormalForm = SPlan2NormalForm_InsertStyle.rewriteSPlan(sroots) // SPlan2NormalForm.rewriteSPlan(sroots)
        sroots = result2NormalForm.replace(sroots)

        if( result2NormalForm != SPlanRewriter.RewriterResult.NoChange ) {
            sroots = NormalFormExploreEq().rewriteSPlan(sroots).replace(sroots)
            if( SPlanRewriteRule.LOG.isTraceEnabled )
                SPlanRewriteRule.LOG.trace("After processing normal form: "+Explain.explainSPlan(sroots))
        }

        //re-construct modified HOP DAG
//        sroots = SPlan2HopReady.rewriteSPlan(sroots).replace(sroots) // put in SPlan2Hop
        var roots2 = SPlan2Hop.splan2Hop(sroots)

        val baseInputs2 = sroots.map { sroot ->
            dimsToInputDims(sroot)
        }
        if( LOG.isTraceEnabled ) {
            LOG.trace("Base input map: ${baseInputs.mapIndexed {i, bil -> "\nr$i\t${bil.mapIndexed { d, bi -> "d$d: ${bi.entries().groupBy { it.key }.map { "(${it.key.hopID})${it.key.opString}=${it.value.map { it.value }}" }.joinToString()}"}.joinToString("\n\t")}"}}" +
                      "\nBase input map2: ${baseInputs2.mapIndexed {i, bil -> "\nr$i\t${bil.mapIndexed { d, bi -> "d$d: ${bi.entries().groupBy { it.key }.map { "(${it.key.hopID})${it.key.opString}=${it.value.map { it.value }}" }.joinToString()}"}.joinToString("\n\t")}"}}")
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
                                    "\n\t0: ${biu[0].map { (k,_) -> k }.toSet().joinToString { "(${it.hopID})${it.opString}" }}" +
                                    "\n\t1: ${biu[1].map { (k,_) -> k }.toSet().joinToString { "(${it.hopID})${it.opString}" }}" +
                                    "\n\t0: ${biu2[0].map { (k,_) -> k }.toSet().joinToString { "(${it.hopID})${it.opString}" }}" +
                                    "\n\t1: ${biu2[0].map { (k,_) -> k }.toSet().joinToString { "(${it.hopID})${it.opString}" }}")
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

        if (LOG.isTraceEnabled)
            LOG.trace("Spoof2Compiler created modified HOP DAG: \n" + Explain.explainHops(roots2))
        HopDagValidator.validateHopDag(roots2)

        //rewrite after applied sum-product optimizer
        ProgramRewriter(RewriteCommonSubexpressionElimination()).rewriteHopDAG(roots, ProgramRewriteStatus())
        ProgramRewriter(RewriteConstantFolding()).rewriteHopDAG(roots, ProgramRewriteStatus())
//        ProgramRewriter(RewriteAlgebraicSimplificationStatic()).rewriteHopDAG(roots, ProgramRewriteStatus())
        ProgramRewriter(RewriteCommonSubexpressionElimination()).rewriteHopDAG(roots, ProgramRewriteStatus())
        programRewriteHops(roots2, recompile, doDynamicProgramRewriter) // Todo Testing...
        //programRewriteHops(roots2, false, true)
//        if( doDynamicProgramRewriter )
//            RewriteAlgebraicSimplificationDynamic().rewriteHopDAGs(roots2, ProgramRewriteStatus())

        HopDagValidator.validateHopDag(roots2)
        if (LOG.isTraceEnabled)
            LOG.trace("Spoof2Compiler rewritten modified HOP DAG: \n" + Explain.explainHops(roots2))

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







}
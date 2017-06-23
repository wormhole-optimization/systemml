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
import org.apache.sysml.hops.rewrite.HopRewriteUtils
import org.apache.sysml.hops.rewrite.ProgramRewriteStatus
import org.apache.sysml.hops.rewrite.ProgramRewriter
import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.SNodeAggregate
import org.apache.sysml.hops.spoof2.plan.SNodeData
import org.apache.sysml.hops.spoof2.plan.SNodeExt
import org.apache.sysml.hops.spoof2.plan.SNodeNary
import org.apache.sysml.hops.spoof2.plan.SNodeNary.NaryOp
import org.apache.sysml.hops.spoof2.rewrite.BasicSPlanRewriter
import org.apache.sysml.hops.spoof2.rewrite.SNodeRewriteUtils
import org.apache.sysml.parser.DMLProgram
import org.apache.sysml.parser.ForStatement
import org.apache.sysml.parser.ForStatementBlock
import org.apache.sysml.parser.FunctionStatement
import org.apache.sysml.parser.FunctionStatementBlock
import org.apache.sysml.parser.IfStatement
import org.apache.sysml.parser.IfStatementBlock
import org.apache.sysml.parser.LanguageException
import org.apache.sysml.parser.StatementBlock
import org.apache.sysml.parser.WhileStatement
import org.apache.sysml.parser.WhileStatementBlock
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

        //rewrite after applied sum-product optimizer
        Hop.resetVisitStatus(roots2)
        val rewriter2 = ProgramRewriter(true, true)
        roots2 = rewriter2.rewriteHopDAGs(roots2, ProgramRewriteStatus())

        if (LOG.isTraceEnabled) {
            LOG.trace("Spoof2Compiler rewritten modified HOP DAG: \n" + Explain.explainHops(roots2))
        }

        return roots2
    }


    // during this phase, no one has exposed labels.
    // passing around matrices, vectors, and scalars
    private fun rConstructSumProductPlan(current: Hop, snodeMemo: MutableMap<Hop, SNode>): SNode {
        if (current.isVisited) {
            return snodeMemo[current]!!
        }

        //recursively process child nodes
        val inputs = ArrayList<SNode>()
        for (c in current.input)
            inputs.add(rConstructSumProductPlan(c, snodeMemo))

        //construct node for current hop
        val node: SNode = when( current ) {
            is DataOp -> {
                if (current.isWrite)
                    SNodeData(inputs[0], current)
                else
                    SNodeData(current)
            }
            is LiteralOp -> {
                SNodeData(current)
            }
            is DataGenOp -> {
                SNodeExt(current)
            }
            is ReorgOp -> {
                if (HopRewriteUtils.isTransposeOperation(current))
                    SNodeNary(NaryOp.TRANSPOSE, inputs[0]) // no indices exposed at this point
                else
                    SNodeExt(current, inputs[0])
            }
            is UnaryOp -> {
                if (current.op.name in NaryOp)
                    SNodeNary(NaryOp.valueOf(current.op.name), inputs[0])
                else
                    SNodeExt(current, inputs[0])
            }
            is BinaryOp -> {
                if (current.op.name in NaryOp)
                    SNodeNary(NaryOp.valueOf(current.op.name), inputs)
                else
                    SNodeExt(current, inputs)
            }
            is AggUnaryOp -> {
                SNodeAggregate(current.op, inputs, hashSetOf<String>(), current.direction)
            }
            is AggBinaryOp -> {
                SNodeNary(NaryOp.MMULT, inputs)
            }
            else -> {
                SNodeExt(current, inputs)
//                throw RuntimeException("Error constructing SNode for HOP: ${current.hopID} ${current.opString}.")
            }
        }

        node.updateSchema()

        current.setVisited()
        snodeMemo.put(current, node)

        return node
    }

    private fun rReconstructHopDag(current: SNode, hopMemo: MutableMap<SNode, Hop>): Hop {
        if (current.visited) {
            return hopMemo[current]!!
        }

        //recursively process child nodes
        val inputs = ArrayList<Hop>()
        for (c in current.inputs)
            inputs.add(rReconstructHopDag(c, hopMemo))

        val node: Hop = when( current ) {
            is SNodeData -> {
                if (!current.inputs.isEmpty()) {
                    HopRewriteUtils.replaceChildReference(current.hop,
                            current.hop.input[0], inputs[0], 0)
                }
                current.hop
            }
            is SNodeAggregate -> {
                fun SNode.isScalar() = this.schema.type.isNotEmpty()
                val agg = current

                if (SNodeRewriteUtils.isSNodeNary(agg.inputs[0], NaryOp.MULT)
                        && (agg.isScalar() || agg.inputs[0].schema.type.size == 3)) // todo definitely change this type req
                {
                    //TODO proper handling of schemas to decide upon transpose
                    var input1 = inputs[0].input[0]
                    var input2 = inputs[0].input[1]
                    input1 = if (agg.isScalar() && input1.dim1 > 1)
                        HopRewriteUtils.createTranspose(input1)
                    else
                        input1
                    input2 = if (agg.isScalar() && input2.dim2 > 1)
                        HopRewriteUtils.createTranspose(input2)
                    else
                        input2
                    val node = HopRewriteUtils.createMatrixMultiply(input1, input2)
                    HopRewriteUtils.createUnary(node, OpOp1.CAST_AS_SCALAR)
                } else {
                    val dir = agg.direction
//                    if (agg.schema.type.isEmpty()) // todo also here
//                        Direction.RowCol
//                    else if (agg.schema.type[0] == agg.inputs[0].schema.type[0])
//                        Direction.Row
//                    else
//                        Direction.Col
                    HopRewriteUtils.createAggUnaryOp(inputs[0], agg.op, dir)
                }
            }
            is SNodeNary -> {
                val nary = current
                if (inputs.size == 1) { //unary
                    if (nary.op == NaryOp.TRANSPOSE)
                        HopRewriteUtils.createTranspose(inputs[0]) as Hop
                    else
                        HopRewriteUtils.createUnary(inputs[0], OpOp1.valueOf(nary.op.name))
                } else if (inputs.size == 2) { //binary
                    if( nary.op == NaryOp.MMULT )
                        HopRewriteUtils.createMatrixMultiply(inputs[0], inputs[1])
                    else
                        HopRewriteUtils.createBinary(inputs[0], inputs[1], OpOp2.valueOf(nary.op.name))
                } else if (inputs.size == 3) { //ternary
                    HopRewriteUtils.createTernary(inputs[0], inputs[1],
                            inputs[2], OpOp3.valueOf(nary.op.name))
                } else
                    TODO()
            }
            is SNodeExt -> {
                val node = current.hop
                if (!inputs.isEmpty()) { //robustness datagen
                    HopRewriteUtils.removeAllChildReferences(node)
                    for (c in inputs)
                        node.addInput(c)
                }
                node
            }
            else -> {
                throw RuntimeException("Error constructing Hop for SNode: ${current.id} ${current.toString()}.")
            }
        }

        current.visited = true
        hopMemo.put(current, node)

        return node
    }
}
package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.LiteralOp
import org.apache.sysml.hops.rewrite.HopRewriteUtils
import org.apache.sysml.hops.spoof2.ConstantMatrixUtil
import org.apache.sysml.hops.spoof2.SHash
import org.apache.sysml.hops.spoof2.plan.*
import java.util.ArrayList

/**
 * Multiply by 0, Add 0, Σ 0. Multiply by 1.
 */
class RewriteMultiplyPlusSimplify: SPlanRewriter {

    /* Use a new cache for each Hop DAG optimized. */
    val zeroCache = mutableMapOf<List<Shape>, SNodeData>()


    private fun extractZeroesOnes(node: SNode, zeroes: MutableSet<SNodeData> = mutableSetOf(), ones: MutableSet<SNodeData> = mutableSetOf()): Pair<Set<SNodeData>, Set<SNodeData>> {
        if (node.visited) return zeroes to ones
        node.visited = true
        if (node is SNodeData && node.isLiteral) {
            if (HopRewriteUtils.isLiteralOfValue(node.hop, 0.0)) { zeroes += node }
            else if (HopRewriteUtils.isLiteralOfValue(node.hop, 1.0)) { ones += node }
        }
        else node.inputs.forEach { extractZeroesOnes(it, zeroes, ones) }
        return zeroes to ones
    }

    override fun rewriteSPlan(roots: ArrayList<SNode>): SPlanRewriter.RewriterResult {
        val zeroes = mutableSetOf<SNodeData>()
        val ones = mutableSetOf<SNodeData>()
        roots.forEach { r -> extractZeroesOnes(r, zeroes, ones) }
        val anyZeroChanged = zeroes.map { bubbleUpZero(it, true) }.fold(false, Boolean::or)
        val anyOneChanged = ones.map { handleOne(it) }.fold(false, Boolean::or)
        return if (anyZeroChanged || anyOneChanged) SPlanRewriter.RewriterResult.NewRoots(roots)
        else SPlanRewriter.RewriterResult.NoChange
    }

    private fun bubbleUpZero(zero: SNode, first: Boolean): Boolean {
        var changed = false
        if (!first && SPlanRewriteRule.LOG.isDebugEnabled)
            SPlanRewriteRule.LOG.debug("RewriteMultiplyPlusSimplify * by 0; bubble up 0 elim (${zero.id}) $zero ${zero.schema}")
        zero.parents.toSet().forEach { pa ->
            if (pa is SNodeAggregate && pa.op == Hop.AggOp.SUM) {
                bubbleUpZero(pa, false); changed = true
            } else if (pa is SNodeNary && pa.op == SNodeNary.NaryOp.MULT) {
                bubbleUpZero(pa, false); changed = true
            } else if (pa is SNodeNary && pa.op == SNodeNary.NaryOp.PLUS) {
                changed = true
                if (pa.inputs.all { it == zero }) {
                    bubbleUpZero(pa, false)
                } else {
                    val okToRemove = pa.schema.names.all { n -> pa.inputs.any { it != zero && n in it.schema } }
                    pa.inputs.removeIf { it == zero }
                    zero.parents.removeIf { it == pa }
                    if (!okToRemove) {
                        val newZero = createConstantZero(zero)
                        pa.inputs += newZero
                        newZero.parents += pa
                    } else {
                        if (pa.inputs.size == 1) {
                            val inp = pa.inputs[0]
                            inp.parents -= pa
                            pa.parents.forEach { it.inputs[it.inputs.indexOf(pa)] = inp; inp.parents += it }
                        }
                    }
                }
            } else {
                val newZero = createConstantZero(zero)
                if (newZero !== zero) {
                    changed = true
                    var idx = pa.inputs.indexOf(zero)
                    while (idx != -1) {
                        pa.inputs[idx] = newZero
                        newZero.parents += pa
                        zero.parents -= pa
                        idx = pa.inputs.indexOf(zero)
                    }
                }
            }
        }
        if (!first) {
            zero.parents.clear()
            stripDead(zero)
        }
        return changed
    }

    private fun handleOne(one: SNodeData): Boolean {
        var changed = false
        one.parents.toSet().forEach { pa ->
            if (pa is SNodeNary && pa.op == SNodeNary.NaryOp.MULT) {
                changed = true
                one.parents.removeIf { it == pa }
                pa.inputs.removeIf { it == one }
                if (pa.inputs.isEmpty()) {
                    pa.parents.forEach { it.inputs[it.inputs.indexOf(pa)] = one; one.parents += it }
                } else if (pa.inputs.size == 1) {
                    val inp = pa.inputs[0]
                    inp.parents -= pa
                    pa.parents.forEach { it.inputs[it.inputs.indexOf(pa)] = inp; inp.parents += it }
                }
            }
        }
        if (changed && SPlanRewriteRule.LOG.isDebugEnabled)
            SPlanRewriteRule.LOG.debug("RewriteMultiplyPlusSimplify * by 1; bubble up 1 from (${one.id}) $one ${one.schema}")
        return changed
    }

    // create literalop if scalar
    private fun createConstantZero(zero: SNode): SNode {
        if (zero.schema.isEmpty()) {
            if (zero is SNodeData && zero.isLiteral && HopRewriteUtils.isLiteralOfValue(zero.hop, 0.0)) {
                zeroCache[listOf()] = zero
                return zero
            }
            return zeroCache.getOrPut(listOf()) { SNodeData(LiteralOp(0.0)) }
        }
        val attrPosList = SHash.createAttributePositionList(zero) // todo cache
        val orderedShapes = attrPosList.map { ab -> zero.schema[ab]!! }
        val sndata = zeroCache.getOrPut(orderedShapes) {
            // how do I get the orientation of a vector?
            if (SPlanRewriteRule.LOG.isDebugEnabled)
                SPlanRewriteRule.LOG.debug("RewriteMultiplyPlusSimplify: create all-zero matrix $orderedShapes")
            SNodeData(when (orderedShapes.size) {
                1 -> ConstantMatrixUtil.genMatrixDataGenOp(orderedShapes[0], 1, 0.0)
                2 -> ConstantMatrixUtil.genMatrixDataGenOp(orderedShapes[0], orderedShapes[1], 0.0)
                else -> throw SNodeException(zero, "don't know how to construct all-0 matrix for this node")
            })
        }
        return makeBindAbove(sndata, attrPosList.mapIndexed { i, n -> AU(i) to n }.toMap())
    }

}
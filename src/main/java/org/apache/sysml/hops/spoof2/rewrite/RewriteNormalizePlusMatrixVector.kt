package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.spoof2.ConstantMatrixUtil
import org.apache.sysml.hops.spoof2.plan.AB
import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.SNodeNary
import org.apache.sysml.hops.spoof2.plan.SNodeNary.NaryOp
import org.apache.sysml.hops.spoof2.plan.firstSecond

/**
 * case: add a vector to a matrix
 * multiply the vector by a constant 1 vector to match the dimension of the matrix.
 *
 * Only valid at initial SPlan before other rewrites that give +s more than two inputs.
 */
class RewriteNormalizePlusMatrixVector : SPlanRewriteRule() {

    override fun rewriteNode(parent: SNode, node: SNode, inputPosition: Int): RewriteResult {
        if( node !is SNodeNary || node.op != NaryOp.PLUS ) // todo generalize to other * functions that are semiring to +
            return RewriteResult.NoChange
        val plus: SNodeNary = node
        val (matrix, vector) = getMatrixVectorInput(plus) ?: return RewriteResult.NoChange

        val dimMatch = matrix.schema.names.find { it in vector.schema.names }!! as AB
        val dimNoMatch = matrix.schema.names.find { it != dimMatch }!! as AB
        val shapeNoMatch = matrix.schema[dimNoMatch]!!

        val bind = ConstantMatrixUtil.genBindColumnVector(dimNoMatch, shapeNoMatch, 1.0)
        vector.parents -= plus
        val mult = SNodeNary(NaryOp.MULT, bind, vector)
        plus.inputs[plus.inputs.indexOf(vector)] = mult
        mult.parents += plus

        if (SPlanRewriteRule.LOG.isDebugEnabled)
            SPlanRewriteRule.LOG.debug("RewriteNormalizePlusMatrixVector on plus ${plus.id}, creating constant 1s vector under (${bind.id})")
        return RewriteResult.NewNode(plus)
    }

    private fun getMatrixVectorInput(plus: SNodeNary): Pair<SNode, SNode>? {
        if( plus.inputs.size != 2 )
            return null
        val (i0, i1) = plus.inputs.firstSecond()
        return when {
            i0.schema.size == 2 && i1.schema.size == 1 -> i0 to i1
            i1.schema.size == 2 && i0.schema.size == 1 -> i1 to i0
            else -> null
        }
    }
}

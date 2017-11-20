package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.DataGenOp
import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.LiteralOp
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.plan.SNodeNary.NaryOp
import org.apache.sysml.parser.*

/**
 * case: add a vector to a matrix
 * multiply the vector by a constant 1 vector to match the dimension of the matrix.
 *
 * Only valid at initial SPlan before other rewrites that give +s more than two inputs.
 */
class RewriteNormalizePlusMatrixVector : SPlanRewriteRule() {

    companion object {
        private class BareParseInfo : ParseInfo {
            var _beginLine: Int = -1
            var _beginColumn: Int = -1
            var _endLine: Int = -1
            var _endColumn: Int = -1
            var _text: String? = null
            var _filename: String? = null
            override fun setBeginLine(beginLine: Int) {
                _beginLine = beginLine
            }
            override fun setBeginColumn(beginColumn: Int) {
                _beginColumn = beginColumn
            }
            override fun setEndLine(endLine: Int) {
                _endLine = endLine
            }
            override fun setEndColumn(endColumn: Int) {
                _endColumn = endColumn
            }
            override fun setText(text: String?) {
                _text = text
            }
            override fun setFilename(filename: String?) {
                _filename = filename
            }
            override fun getBeginLine() = _beginLine
            override fun getBeginColumn() = _beginColumn
            override fun getEndLine() = _endLine
            override fun getEndColumn() = _endColumn
            override fun getText() = _text
            override fun getFilename() = _filename
        }
        private val UNIFORM_PARSE_INFO = BareParseInfo().also { it._text = "uniform" }
        private fun genOneVectorParseInfo(nrows: Long): ParseInfo {
            val pi = BareParseInfo()
            pi.text = "rand(lambda=1.0, min=1.0, pdf=uniform, seed=-1, max=1.0, sparsity=1.0, rows=$nrows, cols=1)"
            return pi
        }
        private fun genOneVectorDataGenOp(nrows: Long): DataGenOp {
            val paramExpressions = arrayListOf(
                    ParameterExpression("lambda", DoubleIdentifier(1.0)),
                    ParameterExpression("min", DoubleIdentifier(1.0)),
                    ParameterExpression("pdf", StringIdentifier("uniform", UNIFORM_PARSE_INFO)),
                    ParameterExpression("seed", IntIdentifier(-1)),
                    ParameterExpression("max", DoubleIdentifier(1.0)),
                    ParameterExpression("sparsity", DoubleIdentifier(1.0)),
                    ParameterExpression("rows", IntIdentifier(nrows)),
                    ParameterExpression("cols", IntIdentifier(1))
            )
            val de = DataExpression.getDataExpression("rand", paramExpressions, genOneVectorParseInfo(nrows), null)
            val hopParams = hashMapOf<String,Hop>(
                    "lambda" to LiteralOp(1.0),
                    "min" to LiteralOp(1.0),
                    "pdf" to LiteralOp("uniform"),
                    "seed" to LiteralOp(-1),
                    "max" to LiteralOp(1.0),
                    "sparsity" to LiteralOp(1.0),
                    "rows" to LiteralOp(nrows),
                    "cols" to LiteralOp(1)
            )
            val dgo = DataGenOp(Hop.DataGenMethod.RAND, de, hopParams)
            dgo.rowsInBlock = -1 // TODO? Maybe 1000?
            dgo.colsInBlock = -1
            return dgo
        }
        private fun genBindDataGen(name: AB, nrows: Shape): SNodeBind {
            val dgo = genOneVectorDataGenOp(nrows)
            val snd = SNodeData(dgo)
            val bind = SNodeBind(snd, mapOf(AU.U0 to name))
            return bind
        }
    }

    override fun rewriteNode(parent: SNode, node: SNode, inputPosition: Int): RewriteResult {
        if( node !is SNodeNary || node.op != NaryOp.PLUS ) // todo generalize to other * functions that are semiring to +
            return RewriteResult.NoChange
        val plus: SNodeNary = node
        val (matrix, vector) = getMatrixVectorInput(plus) ?: return RewriteResult.NoChange

        val dimMatch = matrix.schema.names.find { it in vector.schema.names }!! as AB
        val dimNoMatch = matrix.schema.names.find { it != dimMatch }!! as AB
        val shapeNoMatch = matrix.schema[dimNoMatch]!!

        val bind = genBindDataGen(dimNoMatch, shapeNoMatch)
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

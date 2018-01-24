package org.apache.sysml.hops.spoof2

import org.apache.sysml.hops.DataGenOp
import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.LiteralOp
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.parser.*

/**
 * Util for creating a constant matrix whose entries are all the same value.
 */
object ConstantMatrixUtil {

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
    private fun genMatrixParseInfo(nrow: Long, ncol: Long): ParseInfo {
        val pi = BareParseInfo()
        pi.text = "rand(lambda=1.0, min=1.0, pdf=uniform, seed=-1, max=1.0, sparsity=1.0, rows=$nrow, cols=$ncol)"
        return pi
    }

    fun genMatrixDataGenOp(nrow: Long, ncol: Long, fill: Double): DataGenOp {
        val paramExpressions = arrayListOf(
                ParameterExpression("lambda", DoubleIdentifier(1.0)),
                ParameterExpression("min", DoubleIdentifier(fill)),
                ParameterExpression("pdf", StringIdentifier("uniform", UNIFORM_PARSE_INFO)),
                ParameterExpression("seed", IntIdentifier(-1)),
                ParameterExpression("max", DoubleIdentifier(fill)),
                ParameterExpression("sparsity", DoubleIdentifier(1.0)),
                ParameterExpression("rows", IntIdentifier(nrow)),
                ParameterExpression("cols", IntIdentifier(ncol))
        )
        val de = DataExpression.getDataExpression("rand", paramExpressions, genMatrixParseInfo(nrow, ncol), null)
        val hopParams = hashMapOf<String, Hop>(
                "lambda" to LiteralOp(1.0),
                "min" to LiteralOp(fill),
                "pdf" to LiteralOp("uniform"),
                "seed" to LiteralOp(-1),
                "max" to LiteralOp(fill),
                "sparsity" to LiteralOp(1.0),
                "rows" to LiteralOp(nrow),
                "cols" to LiteralOp(ncol)
        )
        val dgo = DataGenOp(Hop.DataGenMethod.RAND, de, hopParams)
        dgo.rowsInBlock = 1000 // TODO? Maybe 1000?
        dgo.colsInBlock = 1000
        return dgo
    }

    fun genBindColumnVector(name: AB, nrows: Shape, fill: Double): SNodeBind {
        val dgo = genMatrixDataGenOp(nrows, 1, fill)
        val snd = SNodeData(dgo)
        val bind = SNodeBind(snd, mapOf(AU.U0 to name))
        return bind
    }

}
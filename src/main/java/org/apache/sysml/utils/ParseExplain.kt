package org.apache.sysml.utils

import org.apache.sysml.hops.*
import org.apache.sysml.hops.Hop.HopsAgg2String
import org.apache.sysml.parser.DataIdentifier
import org.apache.sysml.parser.Expression

object ParseExplain {


    fun explainToHopDag(explainLines: List<String>): ArrayList<Hop> {
        val memo = HashMap<Long, Hop>()
        val literals = HashMap<String, Long>()
        val roots = HashSet<Long>()

        for((index, explainLine) in explainLines.withIndex()) {
            try {
                parseLine(explainLine, memo, literals, roots)
            } catch (e: RuntimeException) {
                throw RuntimeException("Trouble parsing explain line $index: $explainLine", e)
            }
        }

        // todo: restore positive IDs to literals

        return ArrayList(roots.map { memo[it]!! })
    }

    /**
     * 1. id: "485"
     * 2. op name: "TRead lambda", "rix"
     * 3. children group, if any: "", "(441,[1],[10000000],[1],[1])", "(446)"
     * 4. dim1
     * 5. dim2
     * 6. rows in block
     * 7. cols in block
     * 8. nnz
     * 9. data type
     * 10. value type
     */
    // todo - relax to not necessarily need data type and value type
    private val regexLine = Regex("^-*\\((\\d+)\\) (.+?) ?(\\(?[0-9,.\\[\\]]*\\)?) \\[(-?\\d+),(-?\\d+),(-?\\d+),(-?\\d+),(-?\\d+)](\\w)(\\w) \\[.+].*$")

    private fun parseLine(explainLine: String,
                          memo: HashMap<Long, Hop>, literals: HashMap<String, Long>, roots: HashSet<Long>
    ) {
        val match = regexLine.matchEntire(explainLine) ?: throw RuntimeException("no regex match")
//        run {
//            val orig = match.groupValues[0]
//            val groups = match.groupValues.subList(1, match.groupValues.size)
//            println("$orig ==> $groups")
//        }
        val id = match.groupValues[1].toLong()
        val opString = match.groupValues[2]
        val children = parseChildrenString(match.groupValues[3], literals, memo)
        val dim1 = match.groupValues[4].toLong()
        val dim2 = match.groupValues[5].toLong()
        val rowsInBlock = match.groupValues[6].toLong()
        val colsInBlock = match.groupValues[7].toLong()
        val nnz = match.groupValues[8].toLong()
        val dataType = when(match.groupValues[9][0]) {
            'M' -> Expression.DataType.MATRIX
            'S' -> Expression.DataType.SCALAR
            'F' -> Expression.DataType.FRAME
            'O' -> Expression.DataType.OBJECT
            'U' -> Expression.DataType.UNKNOWN
            else -> throw RuntimeException("unrecognized DataType: ${match.groupValues[9]}")
        }
        val valueType = when(match.groupValues[10][0]) {
            'D' -> Expression.ValueType.DOUBLE
            'I' -> Expression.ValueType.INT
            'B' -> Expression.ValueType.BOOLEAN
            'S' -> Expression.ValueType.STRING
            'O' -> Expression.ValueType.OBJECT
            'U' -> Expression.ValueType.UNKNOWN
            else -> throw RuntimeException("unrecognized ValueType: ${match.groupValues[10]}")
        }

        val childrenHops = children.map {
            roots -= it
            memo[it] ?: throw RuntimeException("child $it not declared before this line")
        }

        val hop = createHop(id, opString, childrenHops, dim1, dim2, rowsInBlock, colsInBlock, nnz, dataType, valueType)

        memo.put(id, hop)
        roots += id
    }

    private val IDFIELD = Hop::class.java.getDeclaredField("_ID")!!
    init {
        IDFIELD.isAccessible = true
    }

    private fun parseChildrenString(childrenString: String,
                                    literals: HashMap<String, Long>, memo: HashMap<Long, Hop>
    ): List<Long> {
        if( childrenString.isEmpty() )
            return emptyList()
        if( childrenString[0] != '(' || childrenString.last() != ')' )
            throw RuntimeException("children string is not surrounded by parentheses: $childrenString")

        return childrenString.substring(1, childrenString.length-1).split(",").map { cstr ->
            val len = cstr.length
            if( cstr[0] == '[' && cstr[len-1] == ']' ) { // inline literal child
                val litStr = if( len >= Explain.LITERAL_EXPLAIN_CUTOFF + 5 && cstr.substring(len-5,len-2) == "..." )
                    cstr.substring(1,len-5)
                else
                    cstr.substring(1, len-1)
                if( litStr in literals )
                    literals[litStr]!! // literal exists in cache
                else {
                    // not in cache - create new literal
                    val lit = when {
                        litStr.equals("true", true) || litStr.equals("false", true) ->
                            LiteralOp(litStr.toBoolean())
                        litStr.toLongOrNull() != null -> LiteralOp(litStr.toLong())
                        litStr.toDoubleOrNull() != null -> LiteralOp(litStr.toDouble())
                        else -> LiteralOp(litStr)
                    }
                    val litId = -literals.size - 1L
                    IDFIELD.set(lit, litId)
                    literals.put(litStr, litId)
                    memo.put(litId, lit)
                    litId
                }
            }
            else // normal Hop child
                cstr.toLong()
        }
    }

    private fun createHop(id: Long, opString: String, inp: List<Hop>,
                          dim1: Long, dim2: Long, rowsInBlock: Long, colsInBlock: Long, nnz: Long,
                          dataType: Expression.DataType, valueType: Expression.ValueType
    ): Hop {
        val (firstWord, remainder) = firstWordAndRem(opString)

        // todo create reversed map of these
        if( firstWord.startsWith("u(") && firstWord.last() == ')' ) {
            val op = firstWord.substring(2, firstWord.length-1)
            val op1 =
                    when (op) {
                        "cast_as_scalar" -> Hop.OpOp1.CAST_AS_SCALAR
                        "cast_as_matrix" -> Hop.OpOp1.CAST_AS_MATRIX
                        else -> (Hop.HopsOpOp12String.entries.find { (_,v) -> v == op }
                                ?: throw RuntimeException("Not in OpOp1: $firstWord")).key
                    }
            return UnaryOp(inp[0].name, dataType, valueType, op1, inp[0])
        }

        if( firstWord.startsWith("b(") && firstWord.last() == ')' ) {
            val op = firstWord.substring(2, firstWord.length-1)
            val (op2, _) = Hop.HopsOpOp2String.entries.find { (_,v) -> v == op }
                    ?: throw RuntimeException("Not in OpOp2: $firstWord")
            return BinaryOp(inp[0].name, dataType, valueType, op2, inp[0], inp[1])
        }

        if( firstWord.startsWith("r(") && firstWord.last() == ')' ) {
            val op = firstWord.substring(2, firstWord.length-1)
            val (rop, _) = Hop.HopsTransf2String.entries.find { (_,v) -> v == op }
                    ?: throw RuntimeException("Not in ReOrgOp: $firstWord")
            return ReorgOp(inp[0].name, dataType, valueType, rop, inp[0])
        }

        if( firstWord.startsWith("t(") && firstWord.last() == ')' ) {
            val op = firstWord.substring(2, firstWord.length-1)
            val (top, _) = Hop.HopsOpOp3String.entries.find { (_,v) -> v == op }
                    ?: throw RuntimeException("Not in OpOp3: $firstWord")
            return if( inp.size == 3 )
                TernaryOp(inp[0].name, dataType, valueType, top, inp[0], inp[1], inp[2])
            else
                TernaryOp(inp[0].name, dataType, valueType, top, inp[0], inp[1], inp[2], inp[3], inp[4])
        }

        if( firstWord.startsWith("ba(") && firstWord.last() == ')' ) {
            val op = firstWord.substring(3, firstWord.length-1)
            val (aggOp, op2) = run {
                val (aggOp, aggOpStr) = HopsAgg2String.entries.maxBy { (_, v) ->
                    if (op.startsWith(v) && Hop.HopsOpOp2String.values.contains(op.substring(v.length)))
                        v.length
                    else -1
                }!!
                if( !op.startsWith(aggOpStr) )
                    throw RuntimeException("Cannot find AggOp/OpOp2 of AggBinaryOp in: $firstWord")
                val rem = op.substring(aggOpStr.length)
                val (op2, _) = Hop.HopsOpOp2String.entries.find { (_, v) -> v == rem } ?: throw RuntimeException("Cannot find AggOp/OpOp2 in: $firstWord")
                aggOp to op2
            }
            return AggBinaryOp(inp[0].name, dataType, valueType, op2, aggOp, inp[0], inp[1])
        }

        if( firstWord.startsWith("ua(") && firstWord.last() == ')' ) {
            val op = firstWord.substring(3, firstWord.length-1)
            val (aggStr, dir) = when {
                op.endsWith("RC") -> op.substring(0, op.length-2) to Hop.Direction.RowCol
                op.endsWith("R") -> op.substring(0, op.length-1) to Hop.Direction.Row
                op.endsWith("C") -> op.substring(0, op.length-1) to Hop.Direction.Col
                else -> throw RuntimeException("Cannot find Direction of AggUnaryOp in: $firstWord")
            }
            val (aggOp, _) = Hop.HopsAgg2String.entries.find { (_,v) -> v == aggStr }
                    ?: throw RuntimeException("Cannot find AggOp of AggUnaryOp in: $firstWord")
            return AggUnaryOp(inp[0].name, dataType, valueType, aggOp, dir, inp[0])
        }

        if( firstWord.startsWith("dg(") && firstWord.last() == ')' ) {
            val op = firstWord.substring(3, firstWord.length-1)
            val dg = Hop.DataGenMethod.valueOf(op.toUpperCase())
            val di = DataIdentifier("dg")
            return DataGenOp(dg, di, hashMapOf()) // todo reconstruct DataGen
        }


        val hop = when (firstWord) {
            "TRead" -> DataOp(remainder, dataType, valueType, Hop.DataOpTypes.TRANSIENTREAD,
                    remainder, dim1, dim2, nnz, rowsInBlock, colsInBlock)
            "TWrite" -> DataOp(remainder, dataType, valueType, inp[0], Hop.DataOpTypes.TRANSIENTWRITE,
                    remainder)
            "rix" -> IndexingOp(inp[0].name, dataType, valueType,
                    inp[0], inp[1], inp[2], inp[3], inp[4], true, true) // todo last two params
            else -> throw RuntimeException("Cannot recognize Hop in: $opString")
        }

        hop.dim1 = dim1
        hop.dim2 = dim2
        hop.rowsInBlock = rowsInBlock
        hop.colsInBlock = colsInBlock
        hop.nnz = nnz

        // todo memory estimates

        IDFIELD.set(hop, id)
        return hop
    }

    private fun firstWordAndRem(str: String): Pair<String,String> {
        val idx = str.indexOf(' ')
        return if( idx == -1 ) str to ""
        else str.substring(0, idx) to str.substring(idx, str.length)
    }

}
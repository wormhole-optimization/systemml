package org.apache.sysml.utils

import org.apache.sysml.hops.*
import org.apache.sysml.hops.Hop.HopsAgg2String
import org.apache.sysml.parser.DataIdentifier
import org.apache.sysml.parser.Expression
import java.io.File
import java.io.IOException

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
     * 11. input memory estimate
     * 12. intermediate memory estimate
     * 13. output memory estimate
     * 14. memory estimate
     */
    // todo - relax to not necessarily need data type and value type
    private val regexLine = Regex("^-*\\((\\d+)\\) (.+?) (\\((?:(?:\\d+|\\[.+]),)*(?:\\d+|\\[.+])\\) )?\\[(-?\\d+),(-?\\d+),(-?\\d+),(-?\\d+),(-?\\d+)](\\w)(\\w) \\[(-|\\d+|MAX),(-|\\d+|MAX),(-|\\d+|MAX) -> (-|\\d+MB|MAX)].*$")

    private fun parseLine(explainLine: String,
                          memo: HashMap<Long, Hop>, literals: HashMap<String, Long>, roots: HashSet<Long>
    ) {
        val match = regexLine.matchEntire(explainLine) ?: throw RuntimeException("no regex match")
//        run {
//            val orig = match.groupValues[0]
//            val groups = match.groupValues.subList(1, match.groupValues.size)
//            println("$orig ==> ${groups.withIndex().joinToString(separator = "") { (i,v) -> String.format("\n\t%2d: '%s'", i, v) } }")
//        }
        val id = match.groupValues[1].toLong()
        val opString = match.groupValues[2]
        val tmp = if( match.groupValues[3].isEmpty()) "" else match.groupValues[3].substring(0, match.groupValues[3].length-1)
        val children = parseChildrenString(tmp, literals, memo)
        val dim1 = match.groupValues[4].toLong()
        val dim2 = match.groupValues[5].toLong()
        val rowsInBlock = match.groupValues[6].toInt()
        val colsInBlock = match.groupValues[7].toInt()
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
        val memInput = recoverMem(match.groupValues[11])
        val memIntermediate = recoverMem(match.groupValues[12])
        val memOutput = recoverMem(match.groupValues[13])
        val memAll = recoverMem(match.groupValues[14])

        val childrenHops = children.map {
            roots -= it
            memo[it] ?: throw RuntimeException("child $it not declared before this line")
        }

        val hop = createHop(id, opString, childrenHops, dim1, dim2, rowsInBlock, colsInBlock, nnz, dataType, valueType, literals, memo)

        HOP_FIELD_MEM_INTERMEDIATE.set(hop, memIntermediate)
        HOP_FIELD_MEM_OUTPUT.set(hop, memOutput)
        HOP_FIELD_MEM.set(hop, memAll)

        memo.put(id, hop)
        roots += id
    }

    private fun recoverMem(str: String): Double {
        return when( str ) {
            "MAX" -> OptimizerUtils.DEFAULT_SIZE
            "-" -> -1.0
            else -> (if (str.endsWith("MB")) str.substring(0, str.length-2) else str)
                    .toDouble()*1024*1024
        }
    }

    private val HOP_FIELD_ID = Hop::class.java.getDeclaredField("_ID")!!
    private val HOP_FIELD_MEM = Hop::class.java.getDeclaredField("_memEstimate")!!
    private val HOP_FIELD_MEM_OUTPUT = Hop::class.java.getDeclaredField("_outputMemEstimate")!!
    private val HOP_FIELD_MEM_INTERMEDIATE = Hop::class.java.getDeclaredField("_processingMemEstimate")!!
    init {
        HOP_FIELD_ID.isAccessible = true
        HOP_FIELD_MEM.isAccessible = true
        HOP_FIELD_MEM_OUTPUT.isAccessible = true
        HOP_FIELD_MEM_INTERMEDIATE.isAccessible = true
    }

    private fun parseChildrenString(childrenString: String,
                                    literals: HashMap<String, Long>, memo: HashMap<Long, Hop>
    ): List<Long> {
        if( childrenString.isEmpty() )
            return emptyList()
        if( childrenString[0] != '(' || childrenString.last() != ')' )
            throw RuntimeException("children string is not surrounded by parentheses: $childrenString")

        var newstr = childrenString.substring(1, childrenString.length-1)
                //.replace("[,]","[]")
        while (true) {
            val idx = newstr.indexOf("[,]")
            if( idx == -1 )
                break
            else {
                newstr = newstr.replaceRange(idx, idx+2, "[]")
            }
        }
        return newstr.split(",").map { cstr ->
            val len = cstr.length
            if( cstr[0] == '[' && cstr[len-1] == ']' ) { // inline literal child
                val litStr = if( len >= Explain.LITERAL_EXPLAIN_CUTOFF + 5 && cstr.substring(len-5,len-2) == "..." )
                    cstr.substring(1,len-5)
                else
                    cstr.substring(1, len-1)
                getLiteralOp(litStr, literals, memo)
            }
            else // normal Hop child
                cstr.toLong()
        }
    }

    private fun getLiteralOp(litStr: String, literals: HashMap<String, Long>, memo: HashMap<Long, Hop>): Long {
        return if( litStr in literals )
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
            HOP_FIELD_ID.set(lit, litId)
            literals.put(litStr, litId)
            memo.put(litId, lit)
            litId
        }
    }

    private fun createHop(id: Long, opString: String, inp: List<Hop>,
                          dim1: Long, dim2: Long, rowsInBlock: Int, colsInBlock: Int, nnz: Long,
                          dataType: Expression.DataType, valueType: Expression.ValueType,
                          literals: HashMap<String, Long>, memo: HashMap<Long, Hop>
    ): Hop {
        val (firstWord, remainder) = firstWordAndRem(opString)

        // todo create reversed map of these
        //            "PWrite" -> DataOp(remainder, dataType, valueType, inp[0], Hop.DataOpTypes.PERSISTENTWRITE, remainder)
        // todo last two params

        // todo memory estimates
        val hop = when {
            firstWord.startsWith("u(") && firstWord.last() == ')' -> {
                val op = firstWord.substring(2, firstWord.length - 1)
                val op1 =
                        when (op) {
                            "cast_as_scalar" -> Hop.OpOp1.CAST_AS_SCALAR
                            "cast_as_matrix" -> Hop.OpOp1.CAST_AS_MATRIX
                            "cast_as_int" -> Hop.OpOp1.CAST_AS_INT
                            "cast_as_double" -> Hop.OpOp1.CAST_AS_DOUBLE
                            "cast_as_boolean" -> Hop.OpOp1.CAST_AS_BOOLEAN
                            else -> (Hop.HopsOpOp12String.entries.find { (_, v) -> v == op }
                                    ?: throw RuntimeException("Not in OpOp1: $firstWord")).key
                        }
                UnaryOp(inp[0].name, dataType, valueType, op1, inp[0])
            }
            firstWord.startsWith("b(") && firstWord.last() == ')' -> {
                val op = firstWord.substring(2, firstWord.length - 1)
                val (op2, _) = Hop.HopsOpOp2String.entries.find { (_, v) -> v == op }
                        ?: throw RuntimeException("Not in OpOp2: $firstWord")
                BinaryOp(inp[0].name, dataType, valueType, op2, inp[0], inp[1])
            }
            firstWord.startsWith("r(") && firstWord.last() == ')' -> {
                val op = firstWord.substring(2, firstWord.length - 1)
                val (rop, _) = Hop.HopsTransf2String.entries.find { (_, v) -> v == op }
                        ?: throw RuntimeException("Not in ReOrgOp: $firstWord")
                ReorgOp(inp[0].name, dataType, valueType, rop, inp[0])
            }
            firstWord.startsWith("t(") && firstWord.last() == ')' -> {
                val op = firstWord.substring(2, firstWord.length - 1)
                val (top, _) = Hop.HopsOpOp3String.entries.find { (_, v) -> v == op }
                        ?: throw RuntimeException("Not in OpOp3: $firstWord")
                if (inp.size == 3)
                    TernaryOp(inp[0].name, dataType, valueType, top, inp[0], inp[1], inp[2])
                else
                    TernaryOp(inp[0].name, dataType, valueType, top, inp[0], inp[1], inp[2], inp[3], inp[4])
            }
            firstWord.startsWith("ba(") && firstWord.last() == ')' -> {
                val op = firstWord.substring(3, firstWord.length - 1)
                val (aggOp, op2) = run {
                    val (aggOp, aggOpStr) = HopsAgg2String.entries.maxBy { (_, v) ->
                        if (op.startsWith(v) && Hop.HopsOpOp2String.values.contains(op.substring(v.length)))
                            v.length
                        else -1
                    }!!
                    if (!op.startsWith(aggOpStr))
                        throw RuntimeException("Cannot find AggOp/OpOp2 of AggBinaryOp in: $firstWord")
                    val rem = op.substring(aggOpStr.length)
                    val (op2, _) = Hop.HopsOpOp2String.entries.find { (_, v) -> v == rem } ?: throw RuntimeException("Cannot find AggOp/OpOp2 in: $firstWord")
                    aggOp to op2
                }
                AggBinaryOp(inp[0].name, dataType, valueType, op2, aggOp, inp[0], inp[1])
            }
            firstWord.startsWith("ua(") && firstWord.last() == ')' -> {
                val op = firstWord.substring(3, firstWord.length - 1)
                val (aggStr, dir) = when {
                    op.endsWith("RC") -> op.substring(0, op.length - 2) to Hop.Direction.RowCol
                    op.endsWith("R") -> op.substring(0, op.length - 1) to Hop.Direction.Row
                    op.endsWith("C") -> op.substring(0, op.length - 1) to Hop.Direction.Col
                    else -> throw RuntimeException("Cannot find Direction of AggUnaryOp in: $firstWord")
                }
                val (aggOp, _) = Hop.HopsAgg2String.entries.find { (_, v) -> v == aggStr }
                        ?: throw RuntimeException("Cannot find AggOp of AggUnaryOp in: $firstWord")
                AggUnaryOp(inp[0].name, dataType, valueType, aggOp, dir, inp[0])
            }
            firstWord.startsWith("dg(") && firstWord.last() == ')' -> {
                val op = firstWord.substring(3, firstWord.length - 1)
                val dg = Hop.DataGenMethod.valueOf(op.toUpperCase())
                val di = DataIdentifier("dg")
                DataGenOp(dg, di, hashMapOf("rows" to LiteralOp(dim1), "cols" to LiteralOp(dim2),
                        "lambda" to memo[getLiteralOp("1.0", literals, memo)],
                        "min" to memo[getLiteralOp("1.0", literals, memo)],
                        "pdf" to memo[getLiteralOp("uniform", literals, memo)],
                        "seed" to memo[getLiteralOp("-1", literals, memo)],
                        "max" to memo[getLiteralOp("1.0", literals, memo)],
                        "sparsity" to memo[getLiteralOp("1.0", literals, memo)]
                        )) // todo reconstruct DataGen
            }
            firstWord.startsWith("spoof(") && firstWord.last() == ')' -> { // SPOOF CODEGEN OP
//                val op = firstWord.substring(3, firstWord.length - 1)
                NaryOp(inp[0].name, dataType, valueType, Hop.OpOpN.PRINTF, *inp.plus(LiteralOp(firstWord)).toTypedArray())
            }
            else -> {
                when (firstWord) {
                    "TRead" -> DataOp(remainder, dataType, valueType, Hop.DataOpTypes.TRANSIENTREAD,
                            remainder, dim1, dim2, nnz, rowsInBlock, colsInBlock)
                    "TWrite", "PWrite" -> DataOp(remainder, dataType, valueType, inp[0], Hop.DataOpTypes.TRANSIENTWRITE, remainder)
//            "PWrite" -> DataOp(remainder, dataType, valueType, inp[0], Hop.DataOpTypes.PERSISTENTWRITE, remainder)
                    "rix" -> IndexingOp(inp[0].name, dataType, valueType,
                            inp[0], inp[1], inp[2], inp[3], inp[4], true, true) // todo last two params
                    "lix" -> throw RuntimeException("no support for lix yet")
                    "m(printf)" -> NaryOp(inp[0].name, dataType, valueType, Hop.OpOpN.PRINTF, *inp.toTypedArray())
                    "m(cbind)" -> NaryOp(inp[0].name, dataType, valueType, Hop.OpOpN.CBIND, *inp.toTypedArray())
                    "m(rbind)" -> NaryOp(inp[0].name, dataType, valueType, Hop.OpOpN.RBIND, *inp.toTypedArray())
                    "q(wsloss)" -> QuaternaryOp(inp[0].name, dataType, valueType,
                            Hop.OpOp4.WSLOSS, inp[0], inp[1], inp[2], inp[3], true)
                    "q(wdivmm)" -> QuaternaryOp(inp[0].name, dataType, valueType,
                            Hop.OpOp4.WDIVMM, inp[0], inp[1], inp[2], inp[3], true)
                    "q(wcemm)" -> QuaternaryOp(inp[0].name, dataType, valueType,
                            Hop.OpOp4.WCEMM, inp[0], inp[1], inp[2], inp[3], true)
                    "q(wumm)" -> QuaternaryOp(inp[0].name, dataType, valueType,
                            Hop.OpOp4.WUMM, inp[0], inp[1], inp[2], inp[3], true)
                    "q(wsigmoid)" -> QuaternaryOp(inp[0].name, dataType, valueType,
                            Hop.OpOp4.WSIGMOID, inp[0], inp[1], inp[2], inp[3], true)
                    else -> throw RuntimeException("Cannot recognize Hop in: $opString")
                }
            }
        }

        hop.dim1 = dim1
        hop.dim2 = dim2
        hop.rowsInBlock = rowsInBlock
        hop.colsInBlock = colsInBlock
        hop.nnz = nnz
        // todo memory estimates

        HOP_FIELD_ID.set(hop, id)
        return hop
    }

    private fun firstWordAndRem(str: String): Pair<String,String> {
        val idx = str.indexOf(' ')
        return if( idx == -1 ) str to ""
        else str.substring(0, idx) to str.substring(idx+1, str.length)
    }


    /**
     * Each argument is treated as the path to a file that contains the output of a HopDag Explain.
     * For each file, this method parses the explain dump and writes out a DOT graphical representation to a new file
     * with ".dot" appended to the file name (unless it ends in ".txt", in which case the ".txt" is replaced with ".dot").
     */
    @JvmStatic
    fun main(args: Array<String>) {
        for (fpath in args) {
            val dotpath = (if (fpath.endsWith(".txt")) fpath.substring(0, fpath.length-4) else fpath)
                    .plus(".dot")

            val f = File(fpath)
            println(f)
            if (!f.exists()) {
                System.err.println("File does not exist: $f")
                continue
            }

            val lines: List<String>
            try {
                lines = f.readLines()
            } catch (e: IOException) {
                System.err.println("Trouble reading file $f\n\tdue to $e")
                continue
            }
            val hops: List<Hop>
            try {
                hops = ParseExplain.explainToHopDag(lines)
            } catch (e: Exception) {
                System.err.println("Trouble parsing file $f\n\tdue to $e")
                continue
            }
//            println(Explain.explainHops(hops))

            val dot = Explain.hop2dot(hops)
//            println(dot)
//            println()

            val fout = File(dotpath)
            try {
                fout.writeText(dot.toString())
            } catch (e: IOException) {
                System.err.println("Trouble writing dot to file $fout\n\t due to $e")
                continue
            }
            //dot -Tpdf explain.dot -o explain.pdf && xreader explain.pdf &
        }
    }


}
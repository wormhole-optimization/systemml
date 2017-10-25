package org.apache.sysml.hops.spoof2

import org.apache.sysml.hops.DataOp
import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.LiteralOp
import org.apache.sysml.hops.rewrite.HopRewriteUtils
import org.apache.sysml.hops.spoof2.enu.NormalFormExploreEq
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.*
import org.apache.sysml.parser.Expression
import org.apache.sysml.utils.Explain

/**
 * Construct a Hop DAG from an SPlan DAG.
 */
object SPlan2Hop {
    private val _rulesToHopReady = listOf(
            RewriteMultiplyCSEToPower(), // RewriteNormalForm factorizes, so we can't get powers >2. Need to reposition. // Obsolete by RewriteElementwiseMultiplyChain?
            RewriteSplitMultiplyPlus(),
            RewritePushAggIntoMult(),
            RewriteClearMxM()
            // todo RewriteRestoreCompound - subtract
    )

    /** Whether to invoke the SPlanValidator after every rewrite pass. */
    private const val CHECK = true

    fun splan2Hop(sroots: ArrayList<SNode>): ArrayList<Hop> {
        rewriteToHopReady(sroots)
        
        val roots2 = ArrayList<Hop>()
        SNode.resetVisited(sroots)
        val hopMemo: MutableMap<SNode, Pair<Hop, Map<AU,AB>>> = hashMapOf()
        for (sroot in sroots) {
            val (h,_) = rReconstructHopDag(sroot, hopMemo)
            roots2.add(h)
        }
        return roots2
    }

    private fun rewriteToHopReady(sroots: ArrayList<SNode>) {
        var count = 0
        do {
            count++
            if(CHECK) SPlanValidator.validateSPlan(sroots)
            var changed = SPlanTopDownRewriter.rewriteDown(sroots, _rulesToHopReady)
            changed = SPlanBottomUpRewriter().rewriteSPlan(sroots) is SPlanRewriter.RewriterResult.NewRoots || changed
        } while (changed)

        if(CHECK) SPlanValidator.validateSPlan(sroots)
        if( SPlanRewriteRule.LOG.isTraceEnabled )
            SPlanRewriteRule.LOG.trace("Ran 'to Hop-ready' rewrites $count times to yield: "+ Explain.explainSPlan(sroots))
    }

    private fun reconstructAggregate(agg: SNodeAggregate, hopMemo: MutableMap<SNode, Pair<Hop, Map<AU,AB>>>): Pair<Hop, Map<AU,AB>> {
        val mult = agg.input

        return if( mult is SNodeNary && mult.op == SNodeNary.NaryOp.MULT && agg.op == Hop.AggOp.SUM
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
                hop0 = HopRewriteUtils.createUnary(hop0, Hop.OpOp1.CAST_AS_MATRIX)
                if( Spoof2Compiler.LOG.isTraceEnabled )
                    Spoof2Compiler.LOG.trace("inserted cast_as_matrix id=${hop0.hopID} for left input to AggBinaryOp")
            }
            if( hop1.dataType == Expression.DataType.SCALAR ) {
                hop1 = HopRewriteUtils.createUnary(hop1, Hop.OpOp1.CAST_AS_MATRIX)
                if( Spoof2Compiler.LOG.isTraceEnabled )
                    Spoof2Compiler.LOG.trace("inserted cast_as_matrix id=${hop1.hopID} for right input to AggBinaryOp")
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
                            HopClass.ROW_VECTOR -> {val t = hop0; hop0 = hop1; hop1 = t} //; val tt = mapInput0; mapInput0 = mapInput1; mapInput1 = tt}
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
                                //val tt = mapInput0; mapInput0 = mapInput1; mapInput1 = tt
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
                                if( Spoof2Compiler.LOG.isTraceEnabled )
                                    Spoof2Compiler.LOG.trace("Switch MxM inputs of (${mult.id}) $mult ${mult.schema}")
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
                if( Spoof2Compiler.LOG.isDebugEnabled )
                    Spoof2Compiler.LOG.debug("Casting result of matrix multiply ${mxm.hopID} to scalar")
                mxm = HopRewriteUtils.createUnary(mxm, Hop.OpOp1.CAST_AS_SCALAR)
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
                        val newInput = SNodeNary(SNodeNary.NaryOp.MULT, agg.input, lit)
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
                hop0 = HopRewriteUtils.createUnary(hop0, Hop.OpOp1.CAST_AS_MATRIX)
                if( Spoof2Compiler.LOG.isTraceEnabled )
                    Spoof2Compiler.LOG.trace("inserted cast_as_matrix id=${hop0.hopID} for input to AggUnaryOp")
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
                    if( Spoof2Compiler.LOG.isDebugEnabled )
                        Spoof2Compiler.LOG.debug("Creating transpose on input to ${agg.op} hopid=${hop0.hopID}")
                }
                dir = Hop.Direction.Row
            }

            val ret = HopRewriteUtils.createAggUnaryOp(hop0, agg.op, dir)
            if( Spoof2Compiler.LOG.isTraceEnabled )
                Spoof2Compiler.LOG.trace("Decide direction $dir on input dims [${hop0.dim1},${hop0.dim2}], schema $aggInput, " +
                        "aggregating on ${agg.aggs} by ${agg.op} to schema ${agg.schema} for SNode ${agg.id} and new Hop ${ret.hopID}")
            mi = if( agg.schema.isNotEmpty() ) {
                agg.check(agg.schema.size == 1) {"expect agg to have 0 or 1 attributes in schema: ${agg.id} $agg ${agg.schema}"}
                mapOf(AU.U0 to agg.schema.names.first() as AB)
            }  else mapOf()
            ret to mi
        }
    }

    private fun reconstructNary(nary: SNodeNary, hopMemo: MutableMap<SNode, Pair<Hop, Map<AU,AB>>>): Pair<Hop, Map<AU,AB>> {
        val (hopInputs, mis) = nary.inputs.map { input ->
            rReconstructHopDag(input, hopMemo)
        }.unzip().let { it.first.toMutableList() to it.second.toMutableList() }

        when( nary.op ) {
            SNodeNary.NaryOp.MULT, SNodeNary.NaryOp.PLUS ->
                if(hopInputs.size == 1)
                    return hopInputs[0] to mis[0]
            else -> {}
        }

        if( nary.inputs.size == 2 ) {
            // if joining on two names and both matrices, ensure that they align by possibly transposing one of them
            if (nary.inputs[0].schema.size == 2 && nary.inputs[1].schema.size == 2) {
                if (mis[0][AU.U0]!! != mis[1][AU.U0]!!) {
                    hopInputs[1] = HopRewriteUtils.createTranspose(hopInputs[1])
                    if (Spoof2Compiler.LOG.isDebugEnabled)
                        Spoof2Compiler.LOG.debug("transpose second matrix ${nary.inputs} hopid=${hopInputs[1].hopID} to match matrix element-wise multiply id=${nary.inputs[1].id}")
                }
            }
            // if joining on one name and both vectors, ensure that they align by possibly transposing one of them
            else if (nary.inputs[0].schema.size == 1 && nary.inputs[0].schema == nary.inputs[1].schema) {
                assert(hopInputs[0].classify().isVector)
                assert(hopInputs[1].classify().isVector)
                if (hopInputs[0].classify() != hopInputs[1].classify()) {
                    hopInputs[1] = HopRewriteUtils.createTranspose(hopInputs[1])
                    if (Spoof2Compiler.LOG.isDebugEnabled)
                        Spoof2Compiler.LOG.debug("transpose vector ${nary.inputs[1]} id=${nary.inputs[1].id} hopid=${hopInputs[1].hopID} to match vector element-wise multiply")
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
                        if (Spoof2Compiler.LOG.isDebugEnabled)
                            Spoof2Compiler.LOG.debug("transpose vector $vec to col vector to match vector expansion element-wise multiply on first dimension of matrix $mat")
                    }
                } else if (vec1 == mat2) {
                    // require vector to be row
                    if (hopInputs[1].classify() != HopClass.ROW_VECTOR) {
                        hopInputs[1] = HopRewriteUtils.createTranspose(hopInputs[1])
                        if (Spoof2Compiler.LOG.isDebugEnabled)
                            Spoof2Compiler.LOG.debug("transpose vector $vec to row vector to match vector expansion element-wise multiply on second dimension of matrix $mat")
                    }
                } else throw SNodeException(nary, "attribute name of vector does not match either attribute name of matrix in vector-expansion element-wise multiply")
            }
        }

        // check for outer product: nary(*) between two vectors whose names do not join
        return if( nary.op == SNodeNary.NaryOp.MULT && nary.inputs[0].schema.size == 1 && nary.inputs[1].schema.size == 1
                && nary.inputs[0].schema.names.first() != nary.inputs[1].schema.names.first() ) {
            when( hopInputs[0].classify() ) {
                HopClass.ROW_VECTOR -> {
                    if( hopInputs[1].classify() == HopClass.ROW_VECTOR ) {
                        if( Spoof2Compiler.LOG.isTraceEnabled )
                            Spoof2Compiler.LOG.trace("transposing 2nd input (${hopInputs[1].hopID}) to outer product (${nary.id}) $nary ${nary.schema} - both are ROW; transpose second and swap")
                        hopInputs[1] = HopRewriteUtils.createTranspose(hopInputs[1])
                    }
                    nary.check(hopInputs[1].classify() == HopClass.COL_VECTOR) {"expected outer product but is not: $hopInputs with dims ${hopInputs.map { it.dim1 to it.dim2 }}"}
                    hopInputs.swap(0,1)
                    nary.inputs.swap(0,1)
                }
                HopClass.COL_VECTOR -> {
                    if( hopInputs[1].classify() == HopClass.COL_VECTOR ) {
                        if( Spoof2Compiler.LOG.isTraceEnabled )
                            Spoof2Compiler.LOG.trace("transposing 2nd input (${hopInputs[1].hopID}) to outer product (${nary.id}) $nary ${nary.schema} - both are COL; transpose second")
                        hopInputs[1] = HopRewriteUtils.createTranspose(hopInputs[1])
                    }
                    nary.check(hopInputs[1].classify() == HopClass.ROW_VECTOR){"expected outer product but is not: $hopInputs with dims ${hopInputs.map { it.dim1 to it.dim2 }}"}
                }
                else -> throw SNodeException(nary, "expected outer product but is not: $hopInputs with dims ${hopInputs.map { it.dim1 to it.dim2 }}")
            }
            HopRewriteUtils.createMatrixMultiply(hopInputs[0], hopInputs[1]) to
                    mapOf(AU.U0 to (nary.inputs[0].schema.names.first() as AB), AU.U1 to (nary.inputs[1].schema.names.first() as AB))
        }
        else {
            hopInputs.mapInPlace {
                if( it.dim1 == 1L && it.dim2 == 1L )
                    HopRewriteUtils.createUnary(it, Hop.OpOp1.CAST_AS_SCALAR)
                else it
            }
            when( nary.inputs.size ) {
                1 -> HopRewriteUtils.createUnary(hopInputs[0], Hop.OpOp1.valueOf(nary.op.name)) to mis[0]
                2 -> HopRewriteUtils.createBinary(hopInputs[0], hopInputs[1], Hop.OpOp2.valueOf(nary.op.name)) to if(mis[0].size >= mis[1].size) mis[0] else mis[1]
                3 -> HopRewriteUtils.createTernary(hopInputs[0], hopInputs[1], hopInputs[2], Hop.OpOp3.valueOf(nary.op.name)) to mis[0] // ?
                else -> throw SNodeException(nary, "don't know how to reconstruct a Hop from an nary with ${nary.inputs.size} inputs $nary")
            }
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
                        if (Spoof2Compiler.LOG.isDebugEnabled)
                            Spoof2Compiler.LOG.debug("on $current id=${current.id}, casting input 0 to scalar in order to match previous Write DataOp ${current.hop} hopid=${current.hop.hopID}")
                        current.check(inputs[0].dim1 == 1L && inputs[0].dim2 == 1L) {"attempt to cast to scalar fails because dims are not 1,1 in inputs[0] ${inputs[0]} hopid=${inputs[0].hopID} [${inputs[0].dim1}, ${inputs[0].dim2}]"}
                        inputs[0] = HopRewriteUtils.createUnary(inputs[0], Hop.OpOp1.CAST_AS_SCALAR)
                    } else if (current.hop.dataType != Expression.DataType.SCALAR && inputs[0].dataType == Expression.DataType.SCALAR) {
                        current.check(inputs[0].dim1 <= 0L && inputs[0].dim2 <= 0L) {"attempt to cast to matrix fails because dims are not 0,0 in inputs[0] ${inputs[0]} hopid=${inputs[0].hopID} [${inputs[0].dim1}, ${inputs[0].dim2}]"}
                        if (Spoof2Compiler.LOG.isDebugEnabled)
                            Spoof2Compiler.LOG.debug("on $current id=${current.id}, casting input 0 to matrix in order to match previous Write DataOp ${current.hop} hopid=${current.hop.hopID}")
                        inputs[0] = HopRewriteUtils.createUnary(inputs[0], Hop.OpOp1.CAST_AS_MATRIX)
                    }
                }

                for( i in inputs.indices ) {
                    val oldHopClass = current.hop.input[i]!!.classify() //current.inputHopClasses[i]
                    if( oldHopClass.isVector ) {
                        if( inputs[i].classify() != oldHopClass ) {
                            inputs[i] = HopRewriteUtils.createTranspose(inputs[i])
                            if( Spoof2Compiler.LOG.isDebugEnabled )
                                Spoof2Compiler.LOG.debug("on $current id=${current.id}, created transpose to force orientation to $oldHopClass on input $i")
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
                if( HopRewriteUtils.isUnary(current.hop, Hop.OpOp1.CAST_AS_SCALAR)
                        && inputs[0].dataType.isScalar ) {
                    // skip the cast
                    inputs[0] to mapOf()
                }
                else if( HopRewriteUtils.isUnary(current.hop, Hop.OpOp1.CAST_AS_MATRIX)
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
                                if( Spoof2Compiler.LOG.isTraceEnabled )
                                    Spoof2Compiler.LOG.trace("on $current id=${current.id}, created transpose to force orientation to $oldHopClass on input $i of $current")
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
                    if( Spoof2Compiler.LOG.isTraceEnabled )
                        Spoof2Compiler.LOG.trace("insert transpose at unbind (${current.id}) $current")
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
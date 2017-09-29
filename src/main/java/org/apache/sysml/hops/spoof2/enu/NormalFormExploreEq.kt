package org.apache.sysml.hops.spoof2.enu

import org.apache.commons.logging.LogFactory
import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.LiteralOp
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.SPlanBottomUpRewriter
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriteRule.RewriteResult
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriter
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriter.RewriterResult
import org.apache.sysml.runtime.controlprogram.parfor.util.IDSequence
import org.apache.sysml.utils.Explain
import java.io.File
import java.io.FileWriter
import java.util.*
import java.util.concurrent.atomic.AtomicBoolean
import kotlin.collections.HashSet
import kotlin.collections.component1
import kotlin.collections.component2

/**
 * Fill an E-DAG.
 */
class NormalFormExploreEq : SPlanRewriter {
    companion object {
        private fun normalSpb_Verify(spb: SumProduct.Block) {
            // top-level block is allowed to have aggregates
            if( spb.product == SNodeNary.NaryOp.PLUS ) {
                if( spb.sumBlocks.any { it.op != Hop.AggOp.SUM } )
                    throw SNodeException("unexpected aggregation type in $spb")
                if( spb.sumBlocks.size > 1 )
                    throw SNodeException("too many SumBlocks in $spb")
                spb.edges.forEach { normalSpb_VerifyMult(it, false) }
            } else normalSpb_VerifyMult(spb, true)
        }

        private fun normalSpb_VerifyMult(spb: SumProduct, allowAggs: Boolean) {
            when(spb) {
                is SumProduct.Input -> {}
                is SumProduct.Block -> {
                    if( !allowAggs && spb.sumBlocks.isNotEmpty() )
                        throw SNodeException("found sumBlocks where none expected (sumBlocks should only be at the top in normal form): $spb")
                    if( spb.sumBlocks.any { it.op != Hop.AggOp.SUM } )
                        throw SNodeException("unexpected aggregation type in $spb")
                    if( spb.sumBlocks.size > 1 )
                        throw SNodeException("too many SumBlocks in $spb")
                    if( spb.product != SNodeNary.NaryOp.MULT )
                        throw SNodeException("found a non-MULT product below the PLUS level in normal form: $spb")
                    if( spb.edges.any { it !is SumProduct.Input } )
                        throw SNodeException("found multiple layers of MULT; one layer expected in normal form")
                }
            }
        }

        private fun normalSpb_GetAggs(spb: SumProduct.Block): List<Name> {
            return spb.sumBlocks.flatMap { it.names.names }
        }

        private fun normalSpb_GetPlusInputs(spb: SumProduct.Block): List<SumProduct> {
            return if( spb.product == SNodeNary.NaryOp.PLUS ) spb.edges else listOf(spb)
        }

        // first-level factorization opportunities
        private fun normalSpb_GetFactorOutOfPlus(plusInputs: List<SumProduct>): Int {
            val baseInputs = plusInputs.map { when(it) {
                is SumProduct.Input -> listOf(it)
                is SumProduct.Block -> it.edges as List<SumProduct.Input>
                is ESP -> throw IllegalStateException("unexpected EBlock")
            } }
            var cnt = 0
            for( i in plusInputs.indices )
                for( j in i+1 until plusInputs.size ) {
                    // if the whole terms are equal, count that as a single factorization opportunity
                    if( plusInputs[i] == plusInputs[j] )
                        cnt++
                    else
                        cnt += baseInputs[i].intersect(baseInputs[j]).size
                }
            return cnt
        }

        private fun normalSpb_GetBaseInputsPullableFromPlus(plusInputs: List<SumProduct>): Set<SumProduct.Input> {
            val baseInputs = plusInputs.map { when(it) {
                is SumProduct.Input -> listOf(it)
                is SumProduct.Block -> it.edges as List<SumProduct.Input>
                is ESP -> throw IllegalStateException("unexpected EBlock")
            } }
            return baseInputs.flatten().toSet()
                    .filter { bi ->
                        baseInputs.indexOfFirst { bi in it } != baseInputs.indexOfLast { bi in it }
                    }.toSet()
        }

        private fun normalSpb_GetBaseInputs(spb: SumProduct.Block): List<SumProduct.Input> {
            return if( spb.product == SNodeNary.NaryOp.PLUS )
                spb.edges.flatMap { when(it) {
                    is SumProduct.Input -> listOf(it)
                    is SumProduct.Block -> it.edges as List<SumProduct.Input>
                    is ESP -> throw IllegalStateException("unexpected EBlock")
                } }
            else spb.edges as List<SumProduct.Input>
        }


        private val LOG = LogFactory.getLog(NormalFormExploreEq::class.java)!!
        private val statsAll = mutableListOf<Stats>()
        private val _addedHook = AtomicBoolean(false)
        private fun addHook() {
            if( !_addedHook.getAndSet(true) )
                Runtime.getRuntime().addShutdownHook(object : Thread() {
                    override fun run() {
                        if( LOG.isInfoEnabled ) {
//                            au.com.bytecode.opencsv.CSVWriter
                            if( statsAll.size in 1..9 )
                                LOG.info("Sum-Product stats:\n${statsAll.joinToString("\n")}")
                            val total = Stats()
                            val f = File("stats.tsv")
                            FileWriter(f).buffered().use { writer ->
                                writer.write(Stats.header())
                                writer.newLine()
                                statsAll.forEach { stat ->
                                    writer.write(stat.toCSVString())
                                    writer.write(Stats.sep.toInt())
                                    writer.newLine()
                                    total += stat
                                }
//                                writer.write(total.toCSVString())
//                                writer.newLine()
                            }
                            LOG.info("Sum-Product all stats:\n\t$total") // statsAll.fold(Stats()) {acc, s -> acc += s; acc}

                            @Suppress("NAME_SHADOWING")
                            val inputFreqs = statsAll.fold(mutableMapOf<String,Int>()) { acc, stat ->
                                stat.spbs.fold(acc) { acc, spb ->
                                    spb.getAllInputs().groupBy {
                                        when( it ) {
                                            is SNodeAggregate -> "agg(${it.op}[${it.aggs.size}])"
                                            is SNodeExt -> "ext(${it.hop.javaClass.simpleName})"
                                            is SNodeBind -> "bi[${it.bindings.size}]"
                                            else -> it.toString()
                                        }
                                    }.mapValues { (_, l) -> l.count() }.forEach { s, c ->
                                        acc.put(s, acc.getOrDefault(s, 0) + c)
                                    }
                                    acc
                                }
                                acc
                            }
                            val totalInputs = inputFreqs.values.sum()
                            val fInputAgg = File("stats-inputs.tsv")
                            FileWriter(fInputAgg).buffered().use { writer ->
                                writer.write("input\tcount\tprop")
                                writer.newLine()
                                inputFreqs.forEach { s, c ->
                                    writer.write("$s\t$c\t${Math.round(c.toDouble()/totalInputs*1000).toDouble()/1000}")
                                    writer.newLine()
                                }
                            }

                        }
                    }
                })
        }
    }

    data class Stats(
            var numSP: Int = 0,
            var numInserts: Long = 0L,
            /** # of different agg, plus, multiply ops constructed */
            var numAggPlusMultiply: Long = 0L,
            var numLabels: Long = 0L,
            var numContingencies: Long = 0L,
            var maxCC: Int = 0,
            var considerPlan: Long = 0L,
            val spbs: MutableList<SumProduct.Block> = mutableListOf() // after partitioning by connected components, before factoring
    ) {
        val id = _idSeq.nextID
        operator fun plusAssign(s: Stats) {
            numSP += s.numSP
            numInserts += s.numInserts
            numAggPlusMultiply += s.numAggPlusMultiply
            numLabels += s.numLabels
            numContingencies += s.numContingencies
            maxCC += s.maxCC
            considerPlan += s.considerPlan
            spbs.clear()
        }
        fun reset() {
            numSP = 0
            numInserts = 0
            numAggPlusMultiply = 0
            numLabels = 0
            numContingencies = 0
            maxCC = 0
            considerPlan = 0
            spbs.clear()
        }
        companion object {
            private val _idSeq = IDSequence()
            const val sep: Char = '\t'
            fun header(): String {
                //numPlusInputs: # of inputs to n-ary + (this is 1 if there is no n-ary plus)
                //numUniqueBaseInputsPullableFromPlus: # of unique base inputs that occur in at least two plus terms
                return "id${sep}numSP${sep}numInserts${sep}numAggPlusMultiply${sep}numLabels${sep}numContingencies${sep}maxCC${sep}considerPlan" +
                        "${sep}numAggNames${sep}numPlusInputs${sep}numBaseInputs${sep}numUniqueBaseInputs${sep}numUniqueBaseInputsPullableFromPlus${sep}normalSpb"
            }
        }
        fun toCSVString_Basic(): String {
            return "$id$sep$numSP$sep$numInserts$sep$numAggPlusMultiply$sep$numLabels$sep$numContingencies$sep$maxCC$sep$considerPlan"
        }
        fun toCSVString(): String {
            val s = toCSVString_Basic()
            return spbs.joinToString("\n") { spb ->
                val aggs = NormalFormExploreEq.normalSpb_GetAggs(spb)
                val plusInputs = NormalFormExploreEq.normalSpb_GetPlusInputs(spb)
//                val factorOutOfPlus = NormalFormExploreEq.normalSpb_GetFactorOutOfPlus(plusInputs)
                // a better measure is the number of base inputs that appear in at least 2 terms
                val baseInputs_PullableFromPlus = NormalFormExploreEq.normalSpb_GetBaseInputsPullableFromPlus(plusInputs)
                val baseInputs = NormalFormExploreEq.normalSpb_GetBaseInputs(spb)
                "$s$sep${aggs.size}$sep${plusInputs.size}$sep${baseInputs.size}$sep${baseInputs.toSet().size}$sep${baseInputs_PullableFromPlus.size}" +
                        "$sep${spb.toString_TSVFriendly()}"
            }
        }

         override fun toString(): String {
             return "Stats(id=$id, numSP=$numSP, numInserts=$numInserts, numAggPlusMultiply=$numAggPlusMultiply, numLabels=$numLabels, numContingencies=$numContingencies, maxCC=$maxCC, considerPlan=$considerPlan, " +
                     "#spbs=${spbs.size})"
         }

     }


    val eNodes: ArrayList<ENode> = arrayListOf()
    var stats = Stats()
    val cseElim = SPlanBottomUpRewriter()


    override fun rewriteSPlan(roots: ArrayList<SNode>): RewriterResult {
        // for each sum-product block, place an ENode at the top
        // fill the ENode with different rewrites.
        // do CSE Elim and Bind Unify
        eNodes.clear()
        stats.reset()
        if( !_addedHook.get() )
            addHook()

        if( LOG.isTraceEnabled )
            LOG.trace("before normal form rewriting: "+Explain.explainSPlan(roots))

//        do {
            val skip = HashSet<Long>()
//            var changed = false // this could be due to a partitioning or a real Sum-Product block
            for (root in roots)
                rRewriteSPlan(root, skip, roots)
//                changed = rRewriteSPlan(root, skip) || changed
            SNode.resetVisited(roots)
//        } while( changed && eNodes.isEmpty() )

        if( eNodes.isEmpty() )
            return RewriterResult.NoChange

        if( LOG.isDebugEnabled )
            LOG.debug("$stats")
//        if( LOG.isTraceEnabled )
//            LOG.trace("E-DAG before CSE Elim: "+Explain.explainSPlan(roots))

        SPlanValidator.validateSPlan(roots)
        cseElim.rewriteSPlan(roots)

        // check inputs to ensure that CSE Elim did not change them
        eNodes.forEach { eNode ->
            for (i in eNode.ePaths.indices) {
                eNode.ePaths[i].input = eNode.inputs[i]
            }
        }

        doCosting(roots)

        if( LOG.isTraceEnabled )
            LOG.trace("E-DAG after implementing best plans: "+Explain.explainSPlan(roots))


//        // temporary replace with first such plan, whatever it is
//        eNodes.forEach { eNode ->
//            val chosenInput = eNode.inputs.first()
//            chosenInput.parents.addAll(eNode.parents)
//            eNode.parents.forEach { it.inputs[it.inputs.indexOf(eNode)] = chosenInput }
//            eNode.inputs.forEach {
//                it.parents -= eNode
//                stripDead(it)
//            }
//        }

        statsAll += stats.copy()
        return RewriterResult.NewRoots(roots)
    }

    private fun rRewriteSPlan(node: SNode, skip: HashSet<Long>, roots: List<SNode>): Boolean {
        if (node.visited)
            return false
        var changed = false

        for (i in node.inputs.indices) {
            var child = node.inputs[i]

            if( (child is SNodeAggregate || child is SNodeNary) && child.id !in skip ) {
                val result = rewriteNode(node, child, skip)
                when (result) {
                    RewriteResult.NoChange -> {}
                    is RewriteResult.NewNode -> {
                        child = result.newNode
                        changed = true
//                        if( LOG.isTraceEnabled )
//                            LOG.trace("after factoring a SPB at (${child.id}) $child:"+Explain.explainSPlan(roots, true))
//                        SPlanValidator.validateSPlan(roots, false)
                    }
                }
            }

            //process children recursively after rewrites
            changed = rRewriteSPlan(child, skip, roots) || changed
        }

        node.visited = true
        return changed
    }

    private fun rewriteNode(parent: SNode, node: SNode, skip: HashSet<Long>): RewriteResult {
        if( !SumProduct.isSumProductBlock(node))
            return RewriteResult.NoChange
//        val origSchema = Schema(node.schema)
        val spb = SumProduct.constructBlock(node, parent)
        if( node.schema.names.any { !it.isBound() } )
            throw SNodeException(node, "Found unbound name in Sum-Product block; may not be handled incorrectly. $spb")
        val isTrivialBlock = spb.getAllInputs().size <= 2
        if( LOG.isTraceEnabled )
            LOG.trace("Found Sum-Product Block at (${node.id}) $node:\n"+spb)

        // 0. Check if this normal form can be partitioned into two separate connected components.
        // This occurs if some portion of the multiplies produces a scalar.
        val CCnames = findConnectedNames(spb, spb.allSchema().names.first())
        if( CCnames != spb.allSchema().names.toSet() ) {
            val NCnames = spb.allSchema().names - CCnames
            val CCspb = SumProduct.Block(
                    spb.sumBlocks.map { SumBlock(it.op, it.names.filter { n,_ -> n in CCnames }) }
                            .filter { it.names.isNotEmpty() },
                    spb.product,
                    spb.edges.filter { it.schema.names.any { it in CCnames } }
                            .map { it.deepCopy() }
            )
            val NCspb = SumProduct.Block(
                    spb.sumBlocks.map { SumBlock(it.op, it.names.filter { n,_ -> n in NCnames }) }
                            .filter { it.names.isNotEmpty() },
                    spb.product,
                    spb.edges.filter { it.schema.names.any { it in NCnames } }
                            .map { it.deepCopy() }
            )
            spb.sumBlocks.clear()
            spb.edges.clear()
            spb.edges += CCspb
            spb.edges += NCspb
            spb.refresh()
            if( LOG.isDebugEnabled && !isTrivialBlock )
                LOG.debug("Partition Sum-Product block into disjoint components:\n" +
                        "Component 1: $CCspb\n" +
                        "Component 2: $NCspb")
            return RewriteResult.NewNode(spb.applyToNormalForm(node, false, false)) // these will be handled as disjoint sub-problems in SPlanNormalFormRewriter at next recursion
        }

        // We will factor this spb.
        if( !isTrivialBlock )
            stats.spbs += spb.deepCopy()
        normalSpb_Verify(spb)

        // Create ENode
        val tmp = node.schema.entries.mapIndexed { i, (n,s) -> AU(i) to (n as AB to s) }.toMap()
        val eNodeNameMapping = tmp.mapValues { (_,v) -> v.first }
        val eNode = ENode(tmp)
        val bind = SNodeBind(eNode, eNodeNameMapping)
        node.parents.forEach { it.inputs[it.inputs.indexOf(node)] = bind }
        bind.parents.addAll(node.parents)
        // disconnect and dead code elim the input
        node.parents.clear() // can no longer use applyToNormalForm
//        stripDead(node, spb.getAllInputs()) // performed by constructBlock()

        // 1. Insert all paths into the E-DAG
        val numInserts = factorAndInsertAll(eNode, spb, eNodeNameMapping, skip)

        val top = if( eNode.inputs.size == 1 ) {
            if( (eNode.parents[0] as SNodeBind).bindings != (eNode.inputs[0] as SNodeUnbind).unbindings ) {
                println("hi")
            }
            val bb = eNode.inputs[0].inputs[0]
            bb.parents.removeIf { it == eNode.inputs[0] }
            bind.parents.forEach {
                it.inputs[it.inputs.indexOf(bind)] = bb
                bb.parents += it
            }
            bb
        } else {
            if( LOG.isTraceEnabled )
                LOG.trace("numInserts: $numInserts")
            eNodes += eNode
            stats.numSP++
            stats.numInserts += numInserts
            bind
        }

//        // 2. CSE
//        SPlanBottomUpRewriter().rewriteSPlan(roots)


        return RewriteResult.NewNode(top) //(bind)
    }

    private fun factorAndInsertAll(eNode: ENode, spb: SumProduct.Block, eNodeNameMapping: Map<AU, AB>, skip: HashSet<Long>): Int {
        val allSpbs = factor(spb)
        return insertSaturated(eNode, allSpbs, eNodeNameMapping, skip)
//        allSpbs.forEach { insert(eNode, it, eNodeNameMapping) }
//        return allSpbs.size
    }

    /**
     * @return The number of inserts performed
     */
    private fun factor(spb: SPB): SP {
        return when (spb.product) {
            SNodeNary.NaryOp.PLUS -> factorPlus(spb)
            SNodeNary.NaryOp.MULT -> factorMult(spb)
            else -> throw IllegalStateException("unexpected product type")
        }

    }
    private fun factorPlus(spb: SPB): SP {
        // push down aggregates into the inputs
        if( spb.sumBlocks.isNotEmpty() ) {
            spb.edges.mapInPlace {
                when (it) {
                    is SumProduct.Input -> SumProduct.Block(spb.sumBlocks, SNodeNary.NaryOp.MULT, it)
                    is SumProduct.Block -> {
                        it.unionInSumBlocks(spb.sumBlocks); it.refresh(); it
                    }
                    is ESP -> throw IllegalStateException("unexpected EBlock")
                }
            }
            spb.sumBlocks.clear()
            spb.refresh()
        }

        // factor each input
        spb.edges.mapInPlace { if(it is SPB) factor(it) else it }
        return spb
    }
    private fun factorMult(spb: SPB): SP {
        // Handle constant aggregation; similar to RewritePushAggIntoPlus
        // Eliminate exact matches with literal doubles if possible, otherwise introduce a literal double multiplicand
        val notInInput = spb.aggSchemaNotInEdges()
        if( notInInput.isNotEmpty() ) { // constant aggregation
            @Suppress("UNCHECKED_CAST")
            val litInputs = spb.edges.filter { it is SPI && it.snode is SNodeData && it.snode.isLiteralNumeric }
//                    .map { it as SPI } //(it as SPI).snode as SNodeData }
                    .toMutableList() as MutableList<SPI>

            loop@while( notInInput.isNotEmpty() && litInputs.isNotEmpty() ) {
                for( v in 1L until (1L shl notInInput.size) ) {
                    val selectSchema = notInInput.entries.filterIndexed { p, _ ->
                        v and (1L shl p) != 0L
                    }.run { Schema(this.map { (n,s) -> n to s }) }
                    val tgt = selectSchema.shapes.fold(1.0, Double::div)
                    val exact = litInputs.find {
                        val hop = (it.snode as SNodeData).hop as LiteralOp
                        hop.doubleValue == tgt
                    }
                    if( exact != null ) {
                        // exact match with a literal - eliminate the literal
                        spb.edges -= exact
                        spb.removeAggs(selectSchema)
                        notInInput -= selectSchema
                        litInputs -= exact
                        continue@loop
                    }
                }
                break
            }
            if( notInInput.isNotEmpty() ) {
                if( LOG.isTraceEnabled )
                    LOG.trace("Failed to eliminate constant aggs $notInInput from block $spb")
                val mFactor = notInInput.shapes.prod()
                val lit = SPI(SNodeData(LiteralOp(mFactor)))
                spb.edges += lit
                spb.removeAggs(notInInput)
            }
            spb.refresh()
        }

        if (spb.edgesGroupByIncidentNames().size == 1) {
            // all edges fit in a single group; nothing to do
            return finishFactorMult(spb)
        }

        // 1. Multiply within groups
        spb.edgesGroupByIncidentNames().forEach { (_, edges) ->
            if (edges.size > 1) {
                // Create a Block on just these inputs.
                // Move these inputs to the new block and wire the new block to this block.
                // Push aggregations down if they are not join conditions (present in >1 edge).
                spb.factorEdgesToBlock(edges)
//                if (LOG.isTraceEnabled)
//                    LOG.trace("Isolating edge group\n[${edges.joinToString(",\n")}]")
            }
        }

        // If an aggName does not touch any other aggNames, then it is independent of them. Factor it.
        loop@do {
            val n2an = spb.nameToAdjacentNames()
            for (agg in spb.aggNames()) {
                if (n2an[agg]!!.disjoint(spb.aggNames() - agg)) {
                    val incidentEdges = spb.nameToIncidentEdge()[agg]!!
                    if (incidentEdges.size == spb.edges.size) { // if all edges remaining touch this one, nothing to do.

                    } else {
                        spb.factorEdgesToBlock(incidentEdges)
                        continue@loop
                    }
                }
            }
            break
        } while (true)

        // Done if no aggregations remain
        if (spb.aggNames().isEmpty())
            return finishFactorMult(spb)

        // Determine what variables we could eliminate at this point
        val eligibleAggNames = spb.eligibleAggNames()
        // Prune down to the agg names with minimum degree
        // Dylan: The minimum degree heuristic is very good.
        val tmp = eligibleAggNames.map { it to (spb.nameToAdjacentNames()[it]!!).size - 1 }
        val minDegree = tmp.map { it.second }.min()!!
        check(minDegree <= 2) { "Minimum degree is >2. Will form tensor intermediary. In spb $spb" }
        val minDegreeAggNames = tmp.filter { it.second == minDegree }.map { it.first }

        // fork on the different possible agg names
        val x = minDegreeAggNames.map { elimName ->
            val incidentEdges = spb.nameToIncidentEdge()[elimName]!!
            if( incidentEdges.size == spb.edges.size ) { // if all edges remaining touch this one, nothing to do. // && spb.aggNames().isEmpty()
                finishFactorMult(spb)
            } else {
                val factoredSpb = spb.deepCopy()
                factoredSpb.factorEdgesToBlock(incidentEdges)
                factor(factoredSpb)
            }
        }
        return when {
            x.size == 1 -> x[0]
            x.all { it is ESP } -> ESP(x.flatMap { (it as ESP).blocks }) // flatten
            else -> ESP(x)
        }
    }

    private fun finishFactorMult(spb: SPB): SP {
        spb.edges.mapInPlace { when(it) {
            is SPB -> factor(it)
            is SPI -> it
            is ESP -> throw IllegalStateException("unexpected EBlock")
        } }
        return spb
    }

    private class ConstructState(
            val skip: HashSet<Long>
    ) {
        var changed = false
        var numAggMultiply = 0L
    }

    private fun constructNext(sp: SP, state: ConstructState): SNode {
        return when( sp ) {
            is SPI -> sp.snode
            is SPB -> {
                state.numAggMultiply += sp.sumBlocks.size + if(sp.edges.size > 1) 1 else 0
                val x = sp.constructNoRec(sp.edges.map { constructNext(it, state) })
                state.skip += x.id
                if( x is SNodeAggregate )
                    state.skip += x.input.id
//                if( LOG.isTraceEnabled )
//                    LOG.trace("Construct:\n$sp\n-> (${x.id}) $x @ ${x.cachedCost}"+if(x is SNodeAggregate) " -- (${x.input.id}) ${x.input} @ ${x.input.cachedCost}" else "")
                x
            }
            is ESP -> {
                if( !state.changed ) {
                    if (sp.nextBlock == sp.blocks.size - 1)
                        sp.nextBlock = 0
                    else {
                        sp.nextBlock++
                        state.changed = true
                    }
                }
                constructNext(sp.blocks[sp.nextBlock], state)
            }
        }
    }

    private fun insertSaturated(eNode: ENode, spb: SumProduct, unbindMap: Map<AU, AB>, skip: HashSet<Long>): Int {
        if( LOG.isTraceEnabled )
            LOG.trace("Saturated SPB:\n"+spb)
        val state = ConstructState(skip)
        var inserts = 0
        do {
            state.changed = false
            val construct = constructNext(spb, state)
//            if( LOG.isTraceEnabled )
//                LOG.trace("Insert: "+construct)
            val newTopInput = SNodeUnbind(construct, unbindMap)
            eNode.addNewEPath(newTopInput)
            inserts++
        } while( state.changed )
        stats.numAggPlusMultiply += state.numAggMultiply
        return inserts
    }


    private fun findConnectedNames(spb: SumProduct.Block, name: Name): Set<Name> {
        return mutableSetOf<Name>().also { rFindConnectedNames(spb.nameToAdjacentNames(), name, it) }
    }

    /** Depth first search to find connected names. */
    private fun rFindConnectedNames(adjMap: Map<Name, Set<Name>>, name: Name, foundNames: MutableSet<Name>) {
        val adjacent = adjMap[name] ?: return
        val adjacentNotFound = adjacent - foundNames
        foundNames += adjacentNotFound
        adjacentNotFound.forEach { rFindConnectedNames(adjMap, it, foundNames) }
    }







    private fun doCosting(roots: ArrayList<SNode>) {
        for( root in roots )
            rMarkRooted(root)

        eNodes.sortBy { it.id } // ascending least id to greatest id
        for( eNode in eNodes ) {
            for( ePath in eNode.ePaths ) {
                // compute cost recursively, add this ePath to the labels of significant nodes (nodes with actual cost) along the way
                ePath.costNoContingent = rAddLabels(ePath.input, ePath, setOf())
            }
        }

        if( LOG.isTraceEnabled )
            LOG.trace("E-DAG after labeling: "+Explain.explainSPlan(roots))

        // all contingencies and costs computed.
        // Partition the ENodes into connected components.
        // Find the best EPath for each ENode individually and use this as a baseline.
        // Consider alternative EPaths that are locally suboptimal but allow sharing oppportunities.
        val CCs = partitionByConnectedComponent()
        stats.maxCC = Math.max(stats.maxCC, CCs.maxBy { it.size }?.size ?: 0)
        if( LOG.isTraceEnabled )
            LOG.trace("CCs: "+CCs.map { it.map { it.id } })
        for( CC in CCs )
            findImplementBestPlanForCC(CC)
    }



    private fun rMarkRooted(node: SNode) {
        if( node.onRootPath )
            return
        if( node is ENode )
            return
        node.onRootPath = true
        node.inputs.forEach { rMarkRooted(it) }
    }

    private fun rAddLabels(node: SNode, ePath: EPath, overlappedEPaths: Set<EPath>): SPCost {
        return when {
            node.onRootPath -> {
                // do not include cost of nodes that are required to compute another root; these nodes are always shared
                // do not include recursive costs
                SPCost.ZERO_COST
            }
            node is ENode -> {
                // do not continue past ENode
                SPCost.ZERO_COST
            }
            node.cachedCost != SPCost.ZERO_COST -> {
                val newOverlapped = node.ePathLabels.filter { it.eNode != ePath.eNode && it !in overlappedEPaths }.toSet()
                val allOverlapped = if(newOverlapped.isNotEmpty()) overlappedEPaths + newOverlapped else overlappedEPaths
                val recCost = node.cachedCost + node.inputs.fold(SPCost.ZERO_COST) { acc, input -> acc + rAddLabels(input, ePath, allOverlapped) }

                val newOverlapList = newOverlapped.sortedBy { it.eNode.id }
                for( i in newOverlapList.indices ) {
                    val otherEPath = newOverlapList[i]
                    if( !ePath.contingencyCostMod.containsKey(otherEPath) ) // it could happen that we cross the same ePath in different branches
                        stats.numContingencies++
                    // if an overlappedEPath is selected, it shadows sharing this node.
                    // same story if an EPath from a different ENode also present here is picked.
                    ePath.contingencyCostMod.put(otherEPath,
                            EPath.EPathShare(otherEPath, recCost, node, overlappedEPaths + newOverlapList.subList(0, i)))
                }
                node.ePathLabels += ePath
                stats.numLabels++
                recCost
            }
            else -> {
                node.inputs.fold(SPCost.ZERO_COST) { acc, input -> acc + rAddLabels(input, ePath, overlappedEPaths) }
            }
        }
    }

    private fun partitionByConnectedComponent(): List<List<ENode>> {
        val CCs = ArrayList<List<ENode>>()
        val eNs = ArrayList(eNodes)
        do {
            val last = eNs.removeAt(eNs.size - 1)
            var newContingent = last.getContingentENodes()
            val recContingent = HashSet(newContingent)
            recContingent += last
            do {
                newContingent = newContingent.flatMap { it.getContingentENodes() }.toSet() - newContingent
                recContingent.addAll(newContingent)
            } while (newContingent.isNotEmpty())
            eNs.removeAll(recContingent)
            CCs += recContingent.sortedBy { it.id }
        } while( eNs.isNotEmpty() )
        return CCs
    }

    private fun findImplementBestPlanForCC(CC: List<ENode>) {
        // Consider contingencies
        val CCchoiceBest = ConsiderContingencies(CC, stats).findBestPlan()

        // Implement best plan
        implementPlan(CCchoiceBest)
    }

    /** Consider contingent plans for this connected component of ENodes.
     * @param CC The connected component. */
    class ConsiderContingencies(CC: List<ENode>, val stats: Stats) {
        private val num = CC.size
        private val nodes = CC.toTypedArray()
        private val nodeToIndex = nodes.mapIndexed { i, node -> node to i }.toMap()
        /** The EPaths that should be considered because they may reduce cost. */
        private val nodeContingencies = Array(num) { nodes[it].ePaths.filter { !it.contingencyCostMod.isEmpty } }
        /** The EPath-to-index map for [nodeContingencies] (caching). */
        private val nodeContingencyToIndex = Array(num) { nodeContingencies[it].mapIndexed { i, ePath -> ePath to i }.toMap() }
        /** 0 means that this EPath is allowed; >0 means that this EPath is blacklisted at that position. */
        private val nodeContingencyBlacklist = Array(num) { IntArray(nodeContingencies[it].size) }

        private val localCheapest = Array<EPath>(num) { nodes[it].ePaths.minBy { it.costNoContingent }!! }
        // inital best cost uses the lowest cost path for each ENode individually
        private val best = localCheapest.copyOf()
        private var bestTotalCost: SPCost = SPCost.MAX_COST
//        init {
//            var cum = SPCost.ZERO_COST
//            for( i in 0 until num) {
//                cum += localCheapest[i].costNoContingent
//                for( j in 0 until i) { // take advantage of any contingencies that happen to agree with our choice of path
//                    cum -= localCheapest[i].contingencyCostMod[localCheapest[j]]
//                            ?.fold(SPCost.ZERO_COST) { acc, (_,cost) -> acc + cost }
//                            ?: SPCost.ZERO_COST
//                }
//            }
//            bestTotalCost = cum
//        }
        private val choices = Array<EPath?>(num) {null}

        fun findBestPlan(): Array<EPath> {
            rConsiderContingency(num-1, SPCost.ZERO_COST)
            if( LOG.isTraceEnabled )
                LOG.trace("best plan found for CC ${nodes.map(ENode::id)}: " +
                        "${best.joinToString("\n\t", "\n\t", "\n\t")}@$bestTotalCost; $stats")
            return best
        }

        // pos: decreases from num-1 to -1
        // invariant: choices[pos+1 until num] != null (assigned)
        //            and choiceCumCost is the cummulative cost of those entries
        private fun rConsiderContingency(pos: Int, choiceCumCost: SPCost) {
            if( pos == -1 ) { // base case: we have a complete assignment
                if( choiceCumCost < bestTotalCost ) {
                    System.arraycopy(choices, 0, best, 0, num)
                    bestTotalCost = choiceCumCost
                }
                stats.considerPlan++
                return
            }
            val origChoice = choices[pos] // remember the current assignment so we can restore it later
            // origChoice is null if this position has not been fixed; non-null if it has been fixed
            if( origChoice != null && (origChoice.contingencyCostMod.isEmpty ||
                    nodeContingencyToIndex[pos][origChoice]!!.let { nodeContingencyBlacklist[pos][it] != 0 }) ) {
                // no contingencies for this fixed choice
                rConsiderContingency(pos-1, choiceCumCost + origChoice.costNoContingent)
                return
            }
            // If we did not fix an alternative from a past decision,
            // first try the cheap option, if we won't try it later during the contingencies
            if( origChoice == null && localCheapest[pos] !in nodeContingencies[pos] ) {
                choices[pos] = localCheapest[pos]
                rConsiderContingency(pos-1, choiceCumCost + localCheapest[pos].costNoContingent)
            }
            // Search over contingent ePaths for this fixed choice if we fixed it;
            // otherwise search over over all alternatives choices that are not blacklisted.
            val contingencyList =
                    if( origChoice != null ) listOf(origChoice)
                    else nodeContingencies[pos].filterIndexed { i, ePath ->
                        ePath == localCheapest[pos] || nodeContingencyBlacklist[pos][i] == 0
                    }
            for (chosenPath in contingencyList) {
                choices[pos] = chosenPath
                val (pathShares_groupByENode, fixedSavings) =
                        // cached in the EPath for efficiency; filter to those eNodes that are not yet fixed
                        // for those ENodes that are fixed, if they are fixed to a contingent path, then we save the contingent cost
                        chosenPath.pathShares_groupByENode().let { it ->
                            // partition the pathShares based on whether the ENode has been fixed yet
                            val (fixed, free)
                                    = it.partition { choices[nodeToIndex[it.first]!!] != null }

                            // for all pathShares under ENodes that have been fixed, see if we can reduce cost by sharing their path
                            // This method eliminates pathShares that overlap with another path share that is of >= cost savings
                            val fixedNonOverlap = EPath.filterNotOverlapping(chosenPath,
                                    fixed.flatMap {it.second.flatMap { it.second }})
                            val fixedSavings = fixedNonOverlap.fold(SPCost.ZERO_COST) { acc, pathShare ->
                                acc + pathShare.cost
                            }
                            free to fixedSavings
                        }

                val cSize = pathShares_groupByENode.size
                if( cSize == 0 ) {
                    rConsiderContingency(pos-1, choiceCumCost - fixedSavings + chosenPath.costNoContingent)
                    continue
                }
                if( cSize >= 62 )
                    LOG.warn("Huge number of contingent ENodes: $cSize. The next line may overflow Long.")
                val cSizeMax = (1 shl cSize) - 1
                var indicator = 0L
                val contPathChoiceIdx = IntArray(cSize)
                // loop over the choices of which eNodes we will fix, given by indicator
                do {
                    indicator++
                    // blacklist the contingent ePaths from each eNode we do not set
                    var t0 = 1L
                    for (j in 0 until cSize) {
                        if ((indicator and t0) == 0L) { // if we do not fix this eNode
                            val eNodeGroup = pathShares_groupByENode[j]
                            blacklistContingent(eNodeGroup.first, eNodeGroup.flatShares(), pos)
                            choices[nodeToIndex[eNodeGroup.first]!!] = null
                            contPathChoiceIdx[j] = -1 // for tracing
                        } else { // if we fix this eNode
                            contPathChoiceIdx[j] = 0
                        }
                        t0 = t0 shl 1
                    }

                    // loop over the choices of which contingent we will fix for each eNode that we decided to fix
                    while(true) {
                        var t = 1L
                        var changed = false
                        var cost = chosenPath.costNoContingent
                        // for each eNode, if we choose to fix that eNode, fix it and reduce the cost
                        for (j in 0 until cSize) {
                            val (contNode, contShares) = pathShares_groupByENode[j]

                            if ((indicator and t) != 0L) { // if we fix this eNode
                                // set this eNode to one of the contingent ePaths and reduce cost
                                val contShare = if (!changed) {
                                    if (contPathChoiceIdx[j] < contShares.size) {
                                        val x = contShares[contPathChoiceIdx[j]]
                                        contPathChoiceIdx[j]++
                                        changed = true
                                        x
                                    } else {
                                        contPathChoiceIdx[j] = 0
                                        contShares[0]
                                    }
                                } else if (contPathChoiceIdx[j] < contShares.size)
                                    contShares[contPathChoiceIdx[j]]
                                else
                                    contShares[0]

                                // check if this eNode is on the same path as another contingent cost
//                                testContShareOk(contShare, )
//                                if( contShare.shareNode.ePathLabels.filter {
//                                    it != chosenPath && it.eNode.id > contShare.ePath.eNode.id
//                                }.let { true } )

                                choices[nodeToIndex[contNode]!!] = contShare.first
                                cost -= contShare.sumShares()
                            }
                            t = t shl 1
                        }
                        if( changed )
                            rConsiderContingency(pos-1, choiceCumCost - fixedSavings + cost)
                        t = 1L
                        for (j in 0 until cSize) {
                            if ((indicator and t) != 0L) {
                                val (contNode, _) = pathShares_groupByENode[j]
                                choices[nodeToIndex[contNode]!!] = null
                            }
                            t = t shl 1
                        }
                        if( !changed )
                            break
                    }

                    // whitelist, undoing the blacklist
                    t0 = 1L
                    for (j in 0 until cSize) {
                        // todo optimize to see if changed in indicator+1
                        if ((indicator and t0) == 0L) { // if we do not fix this eNode
                            val eNodeGroup = pathShares_groupByENode[j]
                            whitelistContingent(eNodeGroup.first, eNodeGroup.flatShares(), pos)
                        }
                        t0 = t0 shl 1
                    }
                } while( indicator < cSizeMax )
            } // end for each ePath
            choices[pos] = origChoice
        } // end function


        // remove from consideration the ePaths present here,
        // because an upstream EPath was chosen not to be fixed even though there was a sharing opportunity
        private fun blacklistContingent(blackNode: ENode, blackEdges: List<EPath.EPathShare>, pos: Int) {
            val blackNodeIdx = nodeToIndex[blackNode]!!
            val ncti = nodeContingencyToIndex[blackNodeIdx]
            blackEdges.forEach {
                val blackEdge = it.ePath
                if( blackEdge in ncti ) {
                    val idx = ncti[blackEdge]!!
                    // if not already blacklisted at a higher level
                    if (nodeContingencyBlacklist[blackNodeIdx][idx] == 0)
                        nodeContingencyBlacklist[blackNodeIdx][idx] = pos
                }
            }
        }

        private fun whitelistContingent(blackNode: ENode, blackEdges: List<EPath.EPathShare>, pos: Int) {
            val blackNodeIdx = nodeToIndex[blackNode]!!
            val ncti = nodeContingencyToIndex[blackNodeIdx]
            blackEdges.forEach {
                val blackEdge = it.ePath
                if( blackEdge in ncti ) {
                    val idx = ncti[blackEdge]!!
                    if (nodeContingencyBlacklist[blackNodeIdx][idx] == pos)
                        nodeContingencyBlacklist[blackNodeIdx][idx] = 0
                }
            }
        }

    }

    private fun implementPlan(chosenPaths: Array<EPath>) {
        for( chosenPath in chosenPaths ) {
            val eNode = chosenPath.eNode
            val chosenInput = chosenPath.input
            chosenInput.parents.addAll(eNode.parents)
            eNode.parents.forEach { it.inputs[it.inputs.indexOf(eNode)] = chosenInput }
            eNode.inputs.forEach {
                it.parents -= eNode
                stripDead(it)
            }
        }

    }


}

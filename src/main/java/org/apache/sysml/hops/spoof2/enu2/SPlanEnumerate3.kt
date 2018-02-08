package org.apache.sysml.hops.spoof2.enu2

import org.apache.commons.logging.LogFactory
import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.spoof2.*
import org.apache.sysml.hops.spoof2.enu.ENode
import org.apache.sysml.hops.spoof2.enu2.PrefixRejectTopIter.PrefixRejectZone
import org.apache.sysml.hops.spoof2.enu2.PrefixRejectTopIter.PrefixRejectZone.Companion.orderGenPrz
import org.apache.sysml.hops.spoof2.plan.*
import java.util.*
import kotlin.math.sign

class SPlanEnumerate3(initialRoots: Collection<SNode>) {
    private val _origRoots = initialRoots.toList()
    constructor(vararg inputs: SNode) : this(inputs.asList())
    private val LOG = LogFactory.getLog(SPlanEnumerate3::class.java)!!
    companion object {
        private const val CHECK_BETWEEN_EXPAND = true
        // todo - configuration parameters for whether to expand +, prune, etc.
        private const val SOUND_PRUNE_TENSOR_INTERMEDIATE = true
        private const val UNSOUND_PRUNE_MAX_DEGREE = true
        /** Whether to prune the partitioning of + in factorPlusBase
         * only considering the paritioning that is left-deep, add/mulitply in order of sparsity, with densest last. */
        private const val PRUNE_INSIGNIFICANT_PLUS = true
        /** Whether to prune the partitioning of * in factorMult,
         * only considering the paritioning that is left-deep, add/mulitply in order of sparsity, with densest last. */
        private const val PRUNE_INSIGNIFICANT_TIMES = true
        /** Whether to prune expressions at the end of factorPlusRec that contain the same Graph added multiple times.
         * This should always be inferior to factoring out the repeated term.
         * For example, `A + A` is strictly worse than `A * (1 + 1)`. */
        private const val SOUND_PRUNE_SAME_PLUS = true
        /** If true, at each OR node, immediately select the one that is cheapest locally.
         * Cost is determined by [PlanCost] by adding the cost of every unique child once, via a set. */
        private const val UNSOUND_PRUNE_LOCAL_BYCOST = true
        /** Prune away all but the + factorization that factor the most nonzeros out. */
        private const val UNSOUND_PRUNE_PF_BYNNZ = true
        /** Whether to spend extra time checking the correctness of + factorizations. */
        private const val CHECK = false
        /** Remove all + terms from factorPlus consideration that have an nnz (before Σ) of < this amount. */
        private const val UNSOUND_PRUNE_PF_NNZMIN = 40000
    }

    private val remainingToExpand = HashSet(initialRoots)
    //    private val seen = HashSet<Id>()
//    private val ht: BiMap<Hash, SNode> = HashBiMap.create()
    private val memo: CanonMemo = CanonMemo()
    private val attrPosListMemo = mutableMapOf<Id, List<AB>>()
    private val planCost = PlanCost(NnzInfer(WorstCaseNnz))
    private val basesForExpand = mutableSetOf<SNode>()



    fun expandAll() {
        while( remainingToExpand.isNotEmpty() )
            expand()
        elimianteExcessRoots()
    }

    private fun elimianteExcessRoots() {
        val roots = mutableSetOf<SNode>()
        val memo = mutableSetOf<SNode>()
        basesForExpand.forEach { getRootsAbove(it, memo, roots) }
        roots -= _origRoots
        roots.forEach { stripDead(it) }
    }

    private fun expand() {
        expand(remainingToExpand.removeFirst() ?: return)
        if (CHECK_BETWEEN_EXPAND)
            SPlanValidator.validateSPlan(_origRoots, true, false)
    }

    private fun expand(node: SNode) {
//        if( node in ht.values ) // todo replace with visit flag
//            return

        when( node ) {
            is SNodeData, is SNodeExt -> return node.inputs.indices.forEach { expand(node.inputs[it]) }
            is SNodeUnbind -> return expand(node.input)
            is SNodeBind -> return expand(node.input)
            is OrNode -> return // OrNodes are already expanded.
            is ENode -> throw AssertionError("unexpected ENode")
            is SNodeAggregate -> if (node.op != Hop.AggOp.SUM ) return expand(node.input)
            is SNodeNary -> if (node.op != SNodeNary.NaryOp.MULT && node.op != SNodeNary.NaryOp.PLUS) {
               return node.inputs.indices.forEach { expand(node.inputs[it]) }
            }
        }

        // strip away parents, add parents to result, in same input location
        val pa: List<SNode> = ArrayList(node.parents)
        val paIdx = pa.map {
            val idx = it.inputs.indexOf(node)
            it.inputs.removeAt(idx)
            idx
        }
        node.parents.clear()

        val b: GraphBag = toGraphBag(node)
        val r = factorPlus(b)
        node.check(r is SNodeOption.Some) {"no expansion possible"}
        val rn = (r as SNodeOption.Some).node

        pa.zip(paIdx).forEach { (p, i) ->
            p.inputs.add(i, rn) // adjust orientation?
            rn.parents.add(p)
        }
    }

    // normal form to graph bag
    private fun toGraphBag(node: SNode): GraphBag {
        return if (node is SNodeNary && node.op == SNodeNary.NaryOp.PLUS) {
            // if this node already exists in the memo's values, then it has already been explored.
            // Don't remove parents because these won't be recreated due to memo table.
            memo.ntb.values.find { (_, opt) -> opt is SNodeOption.Some && opt.node == node }
                    ?.let { (existingB, _) ->
                        existingB.orig
                    } ?: node.inputs.map { it.parents -= node; toGraph(it) }
        } else listOf(toGraph(node))
    }

    private fun toGraph(node: SNode): Graph {
        val (aggs0, mult) = if (node is SNodeAggregate && node.op == Hop.AggOp.SUM) {
            memo.ntg.values.find { (_,opt) -> opt is SNodeOption.Some && opt.node == node }
                    ?.let { (existingG,_) ->
                        return existingG.orig
                    }
            node.input.parents -= node
            node.aggs to node.input
        } else Schema() to node
        val aggs = aggs0.toABS()
        val bases = if (mult is SNodeNary && mult.op == SNodeNary.NaryOp.MULT) {
            memo.ntg.values.find { (_,opt) -> opt is SNodeOption.Some && opt.node == mult }
                    ?.let { (existingG,_) ->
                        // there may be an aggregate attached
                        if (aggs.isEmpty())
                            return existingG.orig
                        val newAggs = aggs + existingG.orig.aggs
                        val newOuts = existingG.orig.outs - newAggs
                        return Graph(newOuts, existingG.orig.edges)
                    }
            mult.inputs.forEach { it.parents -= mult }
            mult.inputs
        } else listOf(mult)
        val edges = bases.map { toEdge(it) }
        val outs = edges.flatMap { it.verts }.toSet() - aggs //bases.flatMap { it.schema.toABS() }.toSet() - aggs
        return Graph(outs, edges)
    }

    private fun toEdge(node: SNode): Edge.C {
        var base = toBase(node)
        val attrPosList = SHash.createAttributePositionList(node, attrPosListMemo)
        // if the base has bound schema, then set the base to an Unbind above the base. Postcondition: base is unbound.
        if (base.schema.names.any { it.isBound() }) {
            base = makeUnbindAbove(base, attrPosList.filter { it in base.schema }.mapIndexed { i,a -> AU(i) to a }.toMap())
        }
        basesForExpand += base
        val verts = attrPosList.map { ABS(it, node.schema[it]!!) }
        return Edge.C(base, verts)
    }

    private fun toBase(node0: SNode): SNode {
        var node = node0
        while (node is SNodeBind || node is SNodeUnbind) {
            if (node.parents.isEmpty())
                node.inputs[0].parents -= node
            node = node.inputs[0]
        }
        return node
    }


    /** Derived a new alternative to add to the list of alternatives [alts].
     * If we have a policy to incrementally prune like [UNSOUND_PRUNE_LOCAL_BYCOST],
     * then apply it here. */
    private fun addNewAlternative(alts: MutableSet<SNode>, newAlt: SNode) {
        if (alts.isEmpty()) {
            alts += newAlt
            return
        }
        if (UNSOUND_PRUNE_LOCAL_BYCOST) {
            val a1 = alts.first()
            val c1 = planCost.costRec(a1)
            val c2 = planCost.costRec(newAlt)
            if (c1 <= c2)
                return
            alts.clear()
        }
        alts += newAlt
        return
    }







    private fun factorPlus(b: GraphBag): SNodeOption {
        if (b.size == 1)
            return factorAgg(b[0])
        // compute canonical form, check if canonical form has an SNode, if so adapt the SNode to this one
        memo.adaptFromMemo(b)?.let { return it }
//        if (LOG.isTraceEnabled)
//            LOG.trace("factorPlus B=$b")

        // breakup the + inputs into connected components. Factor each connected component separately, then combine as factored edges.
        val components = b.connectedComponents()
        if (components.size > 1) {
            val ns = components.map { factorPlus(it).toNode() ?: return SNodeOption.None }
            return plusOrderGraphsBySparsity(ns).toOption()
        }

        val (insignificant, significant) = b.groupSame().partition { g ->
            planCost.nnzInfer.infer(g, true) < UNSOUND_PRUNE_PF_NNZMIN
        }
        if (LOG.isTraceEnabled && insignificant.isNotEmpty()) {
            LOG.trace("UNSOUND_PRUNE_PF_NNZMIN: insignificant plans: ${insignificant.size} / ${b.size}")
        }

        val insigNodes = insignificant.map { factorAgg(it).toNode() ?: return SNodeOption.None }
        val insigSum = if (insigNodes.isEmpty()) null else plusOrderGraphsBySparsity(insigNodes)


        val sigSum = if (significant.isEmpty()) null else run {
            if (LOG.isTraceEnabled)
                LOG.trace("Factoring significant:\n\t" + significant.joinToString("\n\t"))
            val alts = mutableSetOf<SNode>()
//        val alpha = MutableDouble(planCost.costRecUpperBound(b))
            factorPlusRec(listOf(), significant, listOf(), 0, 1, 0, alts, mutableSetOf())
            optionOrNode(alts).toNode() ?: return SNodeOption.None
        }

        val r = when {
            insigSum == null -> sigSum!!
            sigSum == null -> insigSum
            else -> makePlusAbove(insigSum, sigSum)
        }.toOption()

        memo.memoize(b, r)
        return r
    }

    private fun <T> List<T>.groupSame() = this.groupBy { it }.flatMap { it.value }

    private data class MutableDouble(var v: Double)


    /**
     * [Bold] and [Bcur] should be ordered so that identical items appear consecutively.
     * [depth] is frontier #; advances when iaddNewAlternative and j finish in a frontier.
     *
     * Output parameter: [alts], the alternatives for computing the GraphBag of [Bold]+[Bcur]+[Bnew].
     */
    private fun factorPlusRec(Bold: GraphBag, Bcur: GraphBag, Bnew: GraphBag, i0: Int, j0: Int, depth: Int,
                              alts: MutableSet<SNode>, factorPlusMemo: MutableSet<Rep>) {
        if (Bcur.isEmpty() && Bnew.isEmpty()) {
            if (SOUND_PRUNE_SAME_PLUS && !Bold.noDups() && !Bold.getDuplicated().all { it.verts.isEmpty() }) {
                if (LOG.isTraceEnabled)
                    LOG.trace("SOUND_PRUNE_SAME_PLUS: $Bold")
                return
            }
//            if (LOG.isTraceEnabled)
//                LOG.trace("finish+: $Bold")
            factorPlusBase(Bold).tryApply { addNewAlternative(alts, it) }
            return
        }
        val (i,j) = run {
            // This section prevents enumerating the same factorizations multiple times.
            // If an item at position i (or j) is the same as the one before it that we chose NOT to factor out,
            // then don't repeat that choice. Move to the next different item instead.
            var i = i0; var j = j0
            while(i < Bcur.size) {
                while (i > 0 && i < Bcur.size && Bcur[i-1] == Bcur[i]) { i++; j = i+1 }
                while (j > i+1 && j < Bcur.size && Bcur[j - 1] == Bcur[j]) j++
                while (j > Bcur.size && j < Bcur.size + Bold.size && Bold[j - Bcur.size - 1] == Bold[j - Bcur.size]) j++
                if (j >= Bcur.size + Bold.size) {
                    i++; j = i+1
                } else break
            }
            i to j
        }
        if (i >= Bcur.size || i == Bcur.size-1 && Bold.isEmpty())
            return factorPlusRec((Bold + Bcur).groupSame(), Bnew.groupSame(), listOf(), 0, 1, depth+1, alts, factorPlusMemo)
//        if (LOG.isTraceEnabled)
//            LOG.trace("depth=$depth, i=$i, j=$j\n\tBold=$Bold\n\tBcur=$Bcur\n\tBnew=$Bnew")
        // 1. Explore not factoring common terms
        factorPlusRec(Bold, Bcur, Bnew, i, j+1, depth, alts, factorPlusMemo)
        // 2. Explore factoring out
        val Gi = Bcur[i]
        val Gj = if (j < Bcur.size) Bcur[j] else Bold[j-Bcur.size]
        val PFITER = if (UNSOUND_PRUNE_PF_BYNNZ) enumOnlyBestPf(Gi, Gj) else enumPlusFactor(Gi, Gj)
        for ((Gf: Graph, hi: Monomorph, hj: Monomorph) in PFITER) {
            if (Gf.edges.isEmpty()) continue
            if (CHECK) {
                checkPlusFactorization(Gf, hi, Gi)
                checkPlusFactorization(Gf, hj, Gj)
            }
            val Bp = mutableListOf<Graph>()
            // if factoring out results in a single edge and it is a factored graphbag, then add all its graphs to Bp
            // otherwise add the graph resulting from factoring out
            Bp += factorOutTerms(Gf, hi, Gi) // lines 11 to 19
            Bp += factorOutTerms(Gf, hj, Gj)

            val Op = Bp.outs()
            if (SOUND_PRUNE_TENSOR_INTERMEDIATE && Op.size > 2) continue

            // put output vertices in order of canonical graph order - ensures compatibility with enumPlusFactor so that it can be factored out later
            val BpSortedC = memo.canonize(Bp).orderCanon()
            val BpEdge = Edge.F(BpSortedC.orig, BpSortedC.orderOuts())
            val Gp = Graph(Gi.outs+Gj.outs, Gf.edges + BpEdge)

            val newBold: GraphBag; val newBcur: GraphBag
            if (j < Bcur.size) { newBold = Bold; newBcur = Bcur - Gi - Gj }
            else { newBold = Bold - Gj; newBcur = Bcur - Gi }
            val newBnew: GraphBag = Bnew + Gp

            // new term formed. See if we already explored this form.
            if (depth >= 1) {
                val newB: GraphBag = newBold + newBcur + newBnew
                val newBcannon = memo.canonize(newB)
                if (newBcannon.rep in factorPlusMemo) continue
                else factorPlusMemo += newBcannon.rep
            }
            // we did not explore this factoring yet
            factorPlusRec(newBold, newBcur, newBnew, i, i+1, depth, alts, factorPlusMemo)
        }
//        return optionOrNode(alts)
    }

    private fun enumPlusFactor(g1: Graph, g2: Graph): Iterator<Triple<Graph, Monomorph, Monomorph>> {
        return EnumPlusFactorAdapter(EnumPlusFactor(g1, g2))
    }

    private fun factorOutTerms(Gf: Graph, h: Monomorph, G: Graph): List<Graph> {
        val Ep = G.rename(h.invert()).edges.bagMinus(Gf.edges)
        if (Ep.size == 1 && Ep[0] is Edge.F) {
            return (Ep[0] as Edge.F).base
        }
        val Vp = Ep.flatMap { it.verts }.toSet()
        val outs = Vp.intersect(Gf.verts + G.outs)
        val aggs = G.aggs - h.values
        val Gp = Graph(outs, Ep)
        assert(aggs == Gp.aggs)
        return listOf(Gp)
    }

    private fun enumOnlyBestPf(g1: Graph, g2: Graph): Iterator<Triple<Graph, Monomorph, Monomorph>> {
        return retainBestPf(EnumPlusFactor(g1, g2)).iterator()
    }

    /**
     * (Unsound) Prune away all but the + factorization that factor the most nonzeros out.
     */
    private fun retainBestPf(epf: EnumPlusFactor): List<Triple<Graph,Monomorph,Monomorph>> {

        fun adapt(si: SubgraphIso): Triple<Graph, Monomorph, Monomorph> =
                EnumPlusFactor.isoToNewGraphMonomorph(si, epf.g1, epf.g2)
        fun sumEdgeNnz(g: Graph): Nnz = g.edges.sumByLong { e ->
            planCost.nnzInfer.infer(e)
        }

        var bestTrip = adapt(epf.top() ?: return listOf())
        var bestNnzFactor = sumEdgeNnz(bestTrip.first)

        while (epf.next() != null) {
            val trip = adapt(epf.top()!!)
            val nnzFactor = sumEdgeNnz(trip.first)
            if (nnzFactor > bestNnzFactor) {
                bestTrip = trip
                bestNnzFactor = nnzFactor
            }
        }

        return listOf(bestTrip)
    }






    private fun factorPlusBase(B: GraphBag): SNodeOption {
        if (B.size == 1) return factorAgg(B[0])
        memo.adaptFromMemo(B)?.let { return it }

        val result: SNodeOption
        if (PRUNE_INSIGNIFICANT_PLUS) {
            val ns = B.map { factorAgg(it).toNode() ?: return SNodeOption.None }
            result = plusOrderGraphsBySparsity(ns).toOption()
        } else {
            val alts = mutableSetOf<SNode>()
            for ((B1, B2) in enumPartition(B)) {
                val r1 = factorPlusBase(B1).toNode() ?: continue
                val r2 = factorPlusBase(B2).toNode()
                        ?: continue // if this is None, then r1 will be dangling. It will be removed after expandAll()
                alts += makePlusAbove(r1, r2)
            }
//        if (alts.isEmpty()) undo(B)
            result = optionOrNode(alts)
        }

        memo.memoize(B, result)
        return result
    }


    /**
     * For each edge group (e.g. matrices, col vectors, row vectors, scalars), add within the group by increasing nnz.
     * Then add across groups, starting with matrices, then vectors, then scalars.
     * @see multOrderEdgesBySparsity
     */
    private fun plusOrderGraphsBySparsity(ns: List<SNode>): SNode {
        val groups = ns.groupBy { it.schema.names }
        val groupsSorted = groups.mapValues { it.value.sortedBy { planCost.nnzInfer.infer(it) } }
        val groupsAdded = groupsSorted.mapValues { (_,nodes) ->
            nodes.subList(1,nodes.size).fold(nodes[0]) { acc, next ->
                makePlusAbove(acc, next)
            }
        }
        val groupsAddedOrdered = groupsAdded.toList().sortedByDescending { (schema,_) -> schema.size }.map { it.second }
        return groupsAddedOrdered.subList(1,groupsAddedOrdered.size).fold(groupsAddedOrdered[0]) { acc, next ->
            makePlusAbove(acc, next)
        }
    }

    private fun <T> enumPartition(l: List<T>): Iterator<Pair<List<T>,List<T>>> {
        val (listOrdered, przs) = orderGenPrz(l)
        return EnumPartition(listOrdered, przs)
    }

    /**
     * Given a list with duplicates grouped consecutively and marked by [przs],
     * iterate over the partitionings of the list into two nonempty subsets, such that every partitioning is enumerated exactly once.
     */
    class EnumPartition<T>(val l: List<T>, val przs: List<PrefixRejectZone>): AbstractIterator<Pair<List<T>, List<T>>>() {
        // detect when some elements in list are equal; don't enumerate the same state more than once
        private var iter = PrefixRejectTopIter(l.size, 1, przs)
        init { setNext(computeSubset()) }

        private fun computeSubset(): Pair<List<T>, List<T>> {
            val t = iter.top()!!
            return l.partitionIndexed { (i, _) -> i in t }
        }

        override fun computeNext() {
            if (iter.next() != null) {
                // break symmetry on exact half split - don't enumerate same set twice
                return if (l.size % 2 == 0 && iter.n == l.size/2 && iter.top()!![0] != 0) done()
                else setNext(computeSubset())
            }
            if (iter.n+1 > l.size/2)
                return done()
            iter = PrefixRejectTopIter(l.size, iter.n+1, przs)
            return setNext(computeSubset())
        }
    }

    private fun factorAgg(g: Graph): SNodeOption {
        if (g.aggs.isEmpty()) return factorMult(g.edges)
        memo.adaptFromMemo(g)?.let { return it }
        val partitions: List<Graph> = partitionByAggCC(g)
        if (partitions.size > 1) {
            val createdNodes = mutableSetOf<SNode>()
            val ep = mutableListOf<Edge>()
            var ok = true
            partitions.forEach { p ->
                if (p.aggs.isEmpty())
                    ep += p.edges
                else {
                    val l = factorAgg(p)
                    memo.memoize(p, l)
                    when (l) {
                        SNodeOption.None -> { ok = false; return@forEach }
                        is SNodeOption.Some -> createdNodes += l.node
                    }
                    val gc = memo.canonize(p)
                    ep += Edge.F(listOf(p), gc.orderVertsCanon(p.outs))
                }
            }
            if (!ok) { // one of the Edges failed (None from factorAgg)
//                createdNodes.forEach { undo(it) }
                return SNodeOption.None
            }
            val r = factorMult(ep)
            memo.memoize(g, r)
//            if (r == SNodeOption.None) {
////                createdNodes.forEach { undo(it) }
//            }
            return r
        }
        if (SOUND_PRUNE_TENSOR_INTERMEDIATE && g.outs.size > 2) return SNodeOption.None
        if (g.aggs.size == 1 || g.edgeGroups().size == 1) {
            val mult = factorMult(g.edges).toNode() ?: return SNodeOption.None
            val agg = makeAggAbove(mult, g.aggs.map(ABS::a).toSet())
            val r = agg.toOption()
            memo.memoize(g, r)
            return r
        }
        val aggsEnu = if (UNSOUND_PRUNE_MAX_DEGREE) {
            val dmap: Map<ABS, Int> = memo.canonize(g).v2ns.filterKeys { it in g.aggs }.mapValues { (_,v) -> v.size }
            val dmax = dmap.values.max()!!
            g.aggs.filter { dmap[it] == dmax }.toSet()
        } else g.aggs
        val alts = mutableSetOf<SNode>()
        for (v in aggsEnu) {
            val gbelow = Graph(g.outs + v, g.edges)
            val below = factorAgg(gbelow)
            below.tryApply { addNewAlternative(alts, makeAggAbove(it, v.a)) }
        }
        val r = optionOrNode(alts)
        memo.memoize(g, r)
        return r
    }

    private fun partitionByAggCC(g: Graph): List<Graph> {
        val aggOneHop = g.buildOneHopMapUndirected(g.aggs)
        val aggCCs = findCCs(aggOneHop, g.aggs)
        val g0 = run {
            val e0 = g.edges.filter { it.verts.disjoint(g.aggs) }
            val o0 = e0.flatMap { it.verts }.toSet()
            Graph(o0, e0)
        }
        val gs = aggCCs.map { aggCC ->
            val ei = g.edges.filter { !it.verts.disjoint(aggCC) }
            val oi = g.outs.intersect(ei.flatMap { it.verts })
            Graph(oi, ei)
        }
        return if (g0.edges.isEmpty()) gs else gs+g0
    }

    private fun factorMult(es: List<Edge>): SNodeOption {
        // TODO - memo for edges - not as complicated as Graphs
        //if (useMemo) memo.adaptFromMemo(es)?.let { return it }
        if (es.isEmpty()) return memo.literalOne.toOption()
        if (es.size == 1) {
            val e = es[0]
            return when (e) {
                is Edge.C -> {
                    val tgtMap = e.verts.mapIndexed{i,abs -> AU(i) to abs.a}.toMap()
                    makeBindAbove(e.base, tgtMap).toOption()
                }
                is Edge.F -> {
                    val opt = factorPlusBase(e.base)
                    if (e.verts.size < 2) opt
                    else opt.map { n ->
                        // transpose if necessary
                        val actual = SHash.createAttributePositionList(n, attrPosListMemo)
                        val expect = e.verts.map(ABS::a)
                        if (expect == actual) n
                        else {
                            val tgt = expect.mapIndexed { i, a -> AU(i) to a }.toMap()
                            val u = makeUnbindAbove(n, tgt)
                            makeBindAbove(u, tgt)
                        }
                    }
                }
            }
        }
        val r: SNodeOption
        if (PRUNE_INSIGNIFICANT_TIMES) {
            r = multOrderEdgesBySparsity(es)
        } else {
            val alts: MutableSet<SNode> = mutableSetOf()
            for ((es1, es2) in enumPartition(es)) {
                if (SOUND_PRUNE_TENSOR_INTERMEDIATE &&
                        (es1.flatMap(Edge::verts).toSet().size > 2 || es2.flatMap(Edge::verts).toSet().size > 2))
                    continue
                val r1 = factorMult(es1).toNode() ?: continue
                val r2 = factorMult(es2).toNode()
                        ?: continue // if this is None, then r1 will be dangling. It will be removed after expandAll()
                alts += makeMultAbove(r1, r2)
            }
//        if (alts.isEmpty()) undo(es)
            r = optionOrNode(alts) // if size 0, indicates dangling nodes.
        }
//        if (useMemo) memo.memoize(es, r)
        return r
    }

    /**
     * For each edge group (e.g. matrices, col vectors, row vectors, scalars), multiply within the group by increasing nnz.
     * Then multiply across groups, starting with matrices, then vectors, then scalars.
     * @see plusOrderGraphsBySparsity
     */
    private fun multOrderEdgesBySparsity(es: List<Edge>): SNodeOption {
        assert(es.size >= 2)
        val remain = kotlin.run {
            val ns = es.map { factorMult(listOf(it)).toNode() ?: return SNodeOption.None }
            val groups = ns.groupBy { it.schema.names }
            val groupsSorted = groups.mapValues { it.value.sortedBy { planCost.nnzInfer.infer(it) } }
            val groupsMult = groupsSorted.mapValues { (_,nodes) ->
                nodes.subList(1,nodes.size).fold(nodes[0]) { acc, next ->
                    makeMultAbove(acc, next)
                }
            }
            groupsMult.toMutableMap()
        }
        // vector that overlaps with matrix - multiply these first, for cases like Aij vj Bjk
        // get names that have a vector on them. Multiply with a matrix that shares that name.
        val fins: MutableList<SNode> = mutableListOf()
        val namesWithVector = remain.filter { it.key.size == 1 }
        for ((ns, v) in namesWithVector) {
            val n = ns.single()
            val ms = remain.keys.find { it.size == 2 && n in it } ?: continue
            val m = remain[ms]!!
            fins += makeMultAbove(v, m)
            remain.remove(ns)
            remain.remove(ms)
        }
        val groupsMultOrdered = remain.toList().sortedByDescending { (schema,_) -> schema.size }.map { it.second }.toMutableList()
        fins.sortBy { planCost.nnzInfer.infer(it) }
        val f1 = if (fins.isEmpty()) {
            groupsMultOrdered.removeAt(0)
        } else fins.reduce { a, b -> makeMultAbove(a,b) }
        return groupsMultOrdered.fold(f1) { acc, next ->
            makeMultAbove(acc, next)
        }.toOption()
    }



    private fun optionOrNode(alts: Set<SNode>): SNodeOption {
        val sNodeOption = when (alts.size) {
            0 -> SNodeOption.None
            1 -> alts.single().toOption()
            else -> OrNode(alts).toOption() //be careful about flattening - maybe it is okay. Check if a lower OrNode has pointers to it from the memo table; if so, need to rewire to top OrNode.
        }
        return sNodeOption
    }

}


package org.apache.sysml.hops.spoof2.rewrite

import org.apache.commons.logging.LogFactory
import org.apache.log4j.Level
import org.apache.log4j.Logger
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.SPlanRewriter.RewriterResult
import java.util.ArrayList
import java.util.HashMap
import org.apache.sysml.hops.spoof2.rewrite.RewriteBindUnify.Companion.isBindOrUnbind

/**
 * Eliminate Common Sub-Expressions.
 *
 * If mergeLeaves is true, SNodes with no input are merged according to type:
 * literal SNodeDatas are merged if they have the same data type and value;
 * SNodeData reads and SNodeExr are merged if they have the same hop id.
 *
 * Two parents of the same type and same children are merged into one, as follows:
 * ```
 *  X  Y  ->  X   Y
 *  |  |  ->   \ /
 *  f  f  ->    f
 * | \/ | ->   / \
 * | /\ | ->  A   B
 *  A  B  ->
 * ```
 *
 * @param mergeLeaves Whether to do an additional pass to merge leaf nodes (reads, literals, ext)
 * @param structural Whether to rewrite by share equivalence / structure.
 */
class SPlanCSEElimRewriter(
        val mergeLeaves: Boolean = true,
        val structural: Boolean = false
) : SPlanRewriter {

    companion object {
        /** Whether to invoke the SPlanValidator after every rewrite pass. */
        private const val CHECK = true
        internal val LOG = LogFactory.getLog(SPlanCSEElimRewriter::class.java)!!

        //internal configuration flags
        private const val LDEBUG = true
        init {
            if (LDEBUG) Logger.getLogger(SPlanCSEElimRewriter::class.java).level = Level.TRACE
        }

        private fun SNode.getHopId() = when(this) {
            is SNodeData -> this.hop.hopID
            is SNodeExt -> this.hop.hopID
            else -> throw SNodeException(this, "does not have a hop id")
        }

        private fun replaceWithReal(node: SNode, real: SNode): Int {
            node.parents.forEach {
                it.inputs[it.inputs.indexOf(node)] = real
                real.parents += it
            }
            return node.parents.size
        }

        private fun SNodeData.getLiteralKey() = this.hop.valueType.toString()+'_'+this.hop.name
    }

    override fun rewriteSPlan(roots: ArrayList<SNode>): RewriterResult {
        return rewriteSPlanAndGetLeaves(roots).first
    }

    fun rewriteSPlanAndGetLeaves(roots: ArrayList<SNode>): Pair<RewriterResult, MutableList<SNode>> {
        val dataops = HashMap<Long, SNode>()
        val literalops = HashMap<String, SNode>() //key: <VALUETYPE>_<LITERAL>

        var changedLeaves = 0
        SNode.resetVisited(roots)
        if( mergeLeaves ) {
            for (root in roots)
                changedLeaves += rCSEElim_Leaves(root, dataops, literalops)
            SNode.resetVisited(roots)
        }
        var changed = 0
        for (root in roots)
            changed += rCSEElim(root)
        SNode.resetVisited(roots)
        if( CHECK )
            SPlanValidator.validateSPlan(roots)

        val rr = if( changed + changedLeaves > 0 ) {
            if( LOG.isTraceEnabled )
                LOG.trace("Eliminate $changedLeaves leaf and $changed internal node CSEs.")
            RewriterResult.NewRoots(roots)
        } else RewriterResult.NoChange
        return rr to (dataops.values + literalops.values).toMutableList()
    }

    private fun rCSEElim_Leaves(node: SNode,
                                dataops: HashMap<Long, SNode>,
                                literalops: HashMap<String, SNode>): Int {
        if( node.visited )
            return 0
        // do children first
        var changed = 0
        for (i in node.inputs.indices) {
            changed += rCSEElim_Leaves(node.inputs[i], dataops, literalops)
        }

        if( node.inputs.isEmpty() ) { // leaf
            val real = if( node is SNodeData && node.isLiteral ) {
                literalops.putIfAbsent(node.getLiteralKey(), node)
            } else {
                dataops.putIfAbsent(node.getHopId(), node)
            }
            if( real != null ) {
                changed += replaceWithReal(node, real)
            }
        }
        node.visited = true
        return changed
    }

    private fun rCSEElim(node: SNode): Int {
        if( node.visited )
            return 0
        // do children first
        var changed = 0
        for (i in node.inputs.indices) {
            changed += rCSEElim(node.inputs[i])
        }

        if( node.parents.size > 1 ) { // multiple consumers
            var i = 0
            while (i < node.parents.size-1) {
                var j = i+1
                while (j < node.parents.size) {
                    val h1 = node.parents[i]
                    val h2 = node.parents[j]
                    if( h1 !== h2 && h1.compare(h2) ) {
                        h2.parents.forEach {
                            it.inputs[it.inputs.indexOf(h2)] = h1
                            h1.parents += it
                        }
                        h2.inputs.forEach {
                            it.parents -= h2
                        }
                        changed++
                    } else if( h1 !== h2 && h1 is SNodeNary && h1.compareCommutative(h2) ) {
                        doElim(h1, h2)
                        changed++
                    } else if( structural && h1 !== h2 && tryStructuralElim(node, h1, h2) )
                        changed++
                    else
                        j++
                }
                i++
            }
        }
        node.visited = true
        return changed
    }

    private fun Map<Int,Name>.namesToPositions(): Map<Name, Int> = this.map { (i, n) -> n to i }.toMap()
    private fun List<Name>.namesToPositions(): Map<Name, Int> = this.mapIndexed { i, n -> n to i }.toMap()

    data class RealAbove(
            val ra: SNode,
            /** construct name mapping from original node schema position to names in real above */
            val schemaMapping: Map<Name, Int>
    )

    private fun case4(below: SNode, nodeUnbind: SNodeUnbind, bind: SNodeBind): Map<Name,Int> {
        val Ninv = below.schema.names.namesToPositions()
        val Binv = bind.bindings.namesToPositions()
        return bind.schema.names.mapIndexed { bp, n ->
            n to if( n in Binv ) {
                Ninv[nodeUnbind.unbindings[bp]]!!
            } else Ninv[nodeUnbind.schema.names[bp]]!!
        }.toMap()
    }

    private fun case23(belowOrBind: SNode): Map<Name, Int> =
            belowOrBind.schema.names.namesToPositions()

    /**
     * Returns a list of parents that should be checked for structural equivalence.
     * The int in the pair is the input index.
     * The schemaMapping in the RealAbove is the mapping of the parent's schema to below's schema.
     */
    private fun getRealAboveSet(below: SNode, node: SNode): Map<Class<SNode>, MutableList<Pair<RealAbove, Int>>> {
        val filter: (SNode) -> Boolean = {
            (it is SNodeNary || it is SNodeAggregate) && it.inputs.size <= 2
        }
        val s = if( node is SNodeBind ) {
            // 3: below <- node<Bind> <- nodeParent
            node.parents.filter(filter).toSet().map { RealAbove(it, case23(node)) to it.inputs.indexOf(node) }.toSet()
        } else if( node is SNodeUnbind ) {
            // 4: below <- node<Unbind> <- bind<Bind> <- top
//            val Ninv = below.schema.names.namesToPositions()
            node.parents.filter { it is SNodeBind }.toSet().flatMap { bind ->
                bind as SNodeBind
//                val Binv = bind.bindings.namesToPositions()
                val sm = case4(below, node, bind)
                bind.parents.filter(filter).map { top ->
                    RealAbove(top, sm) to top.inputs.indexOf(bind)
                }
            }.toSet()
        } else if( filter(node) ) // 2: below <- node
            setOf(RealAbove(node, case23(below)) to node.inputs.indexOf(below))
        else setOf()
        return s.groupBy { it.first.ra.javaClass }.mapValues { (_,v) -> v.toMutableList() }
    }

    /** Pass the other inputs of the multiplys above. */
    private fun findCommonBelow(n1: SNode, n2: SNode): Pair<Map<Name, Int>,Map<Name, Int>>? {
        if( n1 == n2 ) // 2 and 2: 2: n1 <- above
            return case23(n1).let{ it to it }
        if( n1 is SNodeBind ) {
            val n11 = n1.input
            if (n11 == n2) // 3 and 2: 3: n11 <- n1<Bind> <- above; 2: n2 <- above
                return case23(n1) to case23(n2)
            if (n11 is SNodeUnbind) {
                val n111 = n11.input
                if (n111 == n2) // 4 and 2: 4: n111 <- n11<Unbind> <- n1<Bind> <- above; 2: n2 <- above
                    return case4(n111, n11, n1) to case23(n2)
                if (n2 is SNodeBind) {
                    val n22 = n2.input
                    if (n111 == n22) // 4 and 3
                        return case4(n111, n11, n1) to case23(n2)
                    if (n22 is SNodeUnbind) {
                        val n222 = n22.input
                        if (n111 == n222) // 4 and 4
                            return case4(n111, n11, n1) to case4(n222, n22, n2)
                    }
                }
            }
            if (n2 is SNodeBind) {
                val n22 = n2.input
                if (n11 == n22) // 3 and 3
                    return case23(n1) to case23(n2)
                if (n22 is SNodeUnbind) {
                    val n222 = n22.input
                    if (n11 == n222) // 3 and 4
                        return case23(n1) to case4(n222, n22, n2)
                }
            }
        }
        if (n2 is SNodeBind) {
            val n22 = n2.input
            if (n1 == n22) // 2 and 3
                return case23(n1) to case23(n2)
            if (n22 is SNodeUnbind) {
                val n222 = n22.input
                if (n1 == n222) // 2 and 4
                    return case23(n1) to case4(n222, n22, n2)
            }
        }
        return null
    }

    private fun otherInputIndex(idx: Int) = when(idx) {
        0 -> 1
        1 -> 0
        else -> throw AssertionError("unexpected input index: $idx")
    }

    private fun tryStructuralElim(node: SNode, p1: SNode, p2: SNode): Boolean {
        if( !p1.isBindOrUnbind() && !p2.isBindOrUnbind() || node.schema.size > 2 )
            return false
        val rs1 = getRealAboveSet(node, p1)
        val rs2 = getRealAboveSet(node, p2)
        for( jc in rs1.keys.intersect(rs2.keys) ) {
            for ( (r1, idx1) in rs1[jc]!! ) {
                val iter = rs2[jc]!!.iterator()
                inner@ while( iter.hasNext() ) {
                    val (r2, idx2) = iter.next()
                    if( r2.ra.inputs.size != r1.ra.inputs.size || r1.ra == r2.ra )
                        continue
                    when( jc ) {
                        SNodeAggregate::class.java -> {
                            val n1 = r1.ra as SNodeAggregate
                            val n2 = r2.ra as SNodeAggregate
                            if( n1.op != n2.op )
                                continue@inner
                            // we care about the position of the aggregateNames
                            if( n1.aggreateNames.size != n2.aggreateNames.size )
                                continue@inner
                            val i1 = n1.aggreateNames.map { r1.schemaMapping[it]!! }.toSet()
                            val i2 = n2.aggreateNames.map { r2.schemaMapping[it]!! }.toSet()
                            if( i1 == i2 ) {
                                doElim(n1, n2)
                                iter.remove()
                            }
                        }
                        SNodeNary::class.java -> {
                            val n1 = r1.ra as SNodeNary
                            val n2 = r2.ra as SNodeNary
                            if( n1.inputs.size == 1 ) { // we should never have a unary mult, but in case we do...
                                doElim(n1, n2)
                                iter.remove()
                            }
                            assert(n1.inputs.size == 2)
                            // ensure there is a common input, and get the schema mappings from the common input to the multiply nodes
                            val (m1, m2) = findCommonBelow(n1.inputs[otherInputIndex(idx1)], n2.inputs[otherInputIndex(idx2)]) ?: continue@inner
                            // get the common names among the inputs; ensure the positions match
                            val cks1 = r1.schemaMapping.keys.intersect(m1.keys)
                            val cks2 = r2.schemaMapping.keys.intersect(m2.keys)
                            if( cks1.size != cks2.size )
                                continue@inner
                            when( cks1.size ) {
                                0 -> continue@inner
                                1 -> {
                                    val ck1 = cks1.first()
                                    val ck2 = cks2.first()
                                    if(!( r1.schemaMapping[ck1] == r2.schemaMapping[ck2]
                                            && m1[ck1] == m2[ck2] ))
                                        continue@inner
                                }
                                2 -> {
                                    val (v11,v12) = cks1.iterator().let { it.next() to it.next() }
                                    val (v21,v22) = cks2.iterator().let { it.next() to it.next() }
                                    if( (r1.schemaMapping[v11] == m1[v12]) xor (r2.schemaMapping[v21] == m2[v22]) )
                                        continue@inner
                                }
                                else -> throw AssertionError("unexpected number of common keys")
                            }
                            // multiply bindings match. Check for transpose.
                            if( idx1 != idx2 ) {
                                val n2p = ArrayList(n2.parents)
                                n2.parents.clear()
                                val oldSchema = n2.schema.names.mapIndexed { i, s -> i to s }.toMap()
                                n2.inputs.swap(0, 1)
                                n2.refreshSchema()
                                val u = SNodeUnbind(n2, n2.schema.names.mapIndexed { i, s -> i to s }.toMap())
                                val b = SNodeBind(u, oldSchema)
                                b.parents.addAll(n2p)
                                n2p.forEach {
                                    it.inputs[it.inputs.indexOf(n2)] = b
                                }
                            }
                            doElim(n1, n2)
                            iter.remove()
                        }
                        else -> throw AssertionError("unreachable class: $jc $r1 $r2")
                    }
                }
            }
        }

        return false
    }



    private fun doElim(h1: SNode, h2: SNode) {
        if( LOG.isTraceEnabled )
            LOG.trace("Structure CSE merge (${h2.id}) $h2 ${h2.schema} into (${h1.id}) $h1 ${h1.schema}")
        val h2p = ArrayList(h2.parents)
        h2.parents.clear()
        val oldSchema = h2.schema.names.mapIndexed { i, s -> i to s }.toMap()
        val newSchema = h1.schema.names.mapIndexed { i, s -> i to s }.toMap()
        val os = oldSchema.filter { (op,on) -> newSchema[op] != on }
        val ns = newSchema.filterKeys { it in os }
        val u = SNodeUnbind(h1, ns)
        val b = SNodeBind(u, os)
        h2p.forEach {
            it.inputs[it.inputs.indexOf(h2)] = b
            b.parents += it
        }
        h2.inputs.toSet().forEach {
            it.parents.removeIf { it == h2 }
            stripDead(it)
        }

        // schema change upward - if an input has one of these names in its schema, change it
//        val nameMapToOld = ns.map { (np, nn) -> nn to os[np]!! }.toMap()
        // TODO ^^ Shapes change as a result of the rename. Names seem to be fine.
        h2p.forEach { it.refreshSchemasUpward() }
    }

    private fun stripDead(node: SNode) {
        if (node.parents.isEmpty()) {
            node.inputs.toSet().forEach {
                it.parents.removeIf { it == node }
                stripDead(it)
            }
        }
    }
}

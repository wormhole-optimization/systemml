package org.apache.sysml.hops.spoof2

import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.LiteralOp
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.rewrite.*
import org.apache.sysml.hops.spoof2.rewrite.RewriteBindElim.Companion.eliminateNode
import org.apache.sysml.utils.Explain

/**
 * Put an SPlan DAG in normal form.
 */
object SPlan2NormalForm_InsertStyle : SPlanRewriter {
    // replaces the following rules
//    private val _rulesToNormalForm: List<SPlanRewriteRule> = listOf(
//            RewriteMultiplyPlusSimplify(),
//            RewriteSplitCSE(),          // split CSEs when they would block a sum-product rearrangement
//            RewritePullAggAboveMult(),
//            RewriteAggregateElim(),
//            RewriteMultiplyPlusElim(),
//            RewritePullPlusAboveMult(),
//            RewritePushAggIntoPlus()
////            RewritePullAggAbovePlus()
//    )
    /** Whether to invoke the SPlanValidator after every rewrite pass. */
    private const val CHECK = true
    private val LOG = SPlanRewriteRule.LOG
    private const val CHECK_DURING_RECURSION = false
    private const val EXPLAIN_DURING_RECURSION = false
    private val rewritePullAggAboveMult = org.apache.sysml.hops.spoof2.rewrite.RewritePullAggAboveMult()

    override fun rewriteSPlan(roots: ArrayList<SNode>): SPlanRewriter.RewriterResult {
        // classic cse eliminator - could reduce the amount of work to rewrite to normal form.
        val r0 = SPlanCseEliminator.rewriteSPlan(roots, SPlanCseEliminator.Params(false, true)) // maybe set structural to false for performance?
        if( LOG.isTraceEnabled )
            LOG.trace("")
        var changed = false
        SNode.resetVisited(roots)
        for (root in roots) {
            val (newChanged, result) = toNormalForm(root, roots, false)
            changed = newChanged || changed
        }
        SNode.resetVisited(roots)
        if( CHECK )
            SPlanValidator.validateSPlan(roots)
        if (!changed) {
            if (LOG.isTraceEnabled)
                LOG.trace("'SPlan2NormalForm_InsertStyle' rewrites did not affect SNodePlan; skipping rest")
            return SPlanRewriter.RewriterResult.NoChange
        } else {
            if (LOG.isTraceEnabled)
                LOG.trace("'SPlan2NormalForm_InsertStyle' rewrites yield: " + Explain.explainSPlan(roots, true))
            return SPlanRewriter.RewriterResult.NewRoots(roots)
        }
    }

    /**
     * @param copyOnChange Whether to clone the node if there is a significant change. False means change in place. True means copy and apply the change to the copy, then return the copy.
     * @return whether there was a change, and the new node if [copyOnChange] is true and there is any change.
     */
    private fun toNormalForm(_node: SNode, allRoots: List<SNode>, copyOnChange: Boolean): Pair<Boolean, SNode> {
        var node = _node
//        // wait until all children processed
//        if( !node.inputs.all { it.id in resultMap } )
//            return false
        if (node.visited) {
//            SPlanValidator.checkAtBelowVisited(node)
            return false to node
        }
//        if( LOG.isTraceEnabled )
//            LOG.trace("enter children of (${node.id} $node ${node.schema}")
        var changed = false
        val returnedChildren = ArrayList<SNode>(node.inputs.size)
        for (i in node.inputs.indices) {
            val (thisChange, retNode) = toNormalForm(node.inputs[i], allRoots, copyOnChange)
            changed = changed || thisChange
            returnedChildren += retNode
        }
        if (copyOnChange && changed) {
            node = node.shallowCopy(returnedChildren)
        }
//        if( LOG.isTraceEnabled )
//            LOG.trace("at (${node.id}) $node ${node.schema}")
//        node.visited = true
//        try {
//            SPlanValidator.checkAtBelowVisited(node)
//        } catch (e: SNodeException) {
//            LOG.error("\n" + Explain.explainSPlan(allRoots, true), e)
//            throw RuntimeException("at (${node.id}) $node ${node.schema}", e)
//        }
//        node.visited = false
        // inductive hypothesis: each input is in normal form

        // Split input CSEs only if we would modify them. Otherwise allow inputs to have multiple parents.
        val (newChanged, newNode) = when (node) {
            is SNodeNary -> {
                if (node.op == SNodeNary.NaryOp.PLUS) {
                    insertPlus(node) //!copyOnChange || !changed
                } else if (node.op == SNodeNary.NaryOp.MULT) {
                    insertMult(node) //!copyOnChange || !changed
                } else false to node
            }
            is SNodeAggregate -> {
                if (node.op == Hop.AggOp.SUM)
                    insertAgg(node) //!copyOnChange || !changed
                else false to node
            }
            is SNodeBind -> {
                if (node.bindings.isEmpty()) {
                    true to eliminateNode(node)
                } else insertBind(node, false) //!copyOnChange || !changed
            }
            is SNodeUnbind -> {
                if (node.unbindings.isEmpty()) {
                    true to eliminateNode(node)
                } else insertUnbind(node, false) //!copyOnChange || !changed
            }
            else -> false to node
        }
        node = newNode
        node.visited = true
//        SPlanValidator.checkAtBelowVisited(node)

        if (EXPLAIN_DURING_RECURSION && LOG.isTraceEnabled && newChanged)
            LOG.trace(Explain.explainSPlan(allRoots, true))
        if (CHECK_DURING_RECURSION && newChanged)
            SPlanValidator.validateSPlan(allRoots, false)

        // bind/unbind changes are not real changes
        return (changed || newChanged && (copyOnChange || node !is SNodeBind && node !is SNodeUnbind)) to node
    }

    private tailrec fun insertUnbind(unbind: SNodeUnbind, changed: Boolean): Pair<Boolean, SNode> {
        val modify = checkModifyConditionsOnInputs(unbind) { input ->
            input is SNodeUnbind ||
                    (input is SNodeBind && !input.bindings.keys.disjoint(unbind.unbindings.keys))
        }
        if( !modify )
            return changed to unbind
        val bind = unbind.input
        when (bind) {
            is SNodeUnbind -> { // unbind-unbind
                bind.unbindings += unbind.unbindings
                bind.refreshSchema()
                eliminateNode(unbind)
                if (LOG.isTraceEnabled)
                    LOG.trace("SPlan2NormalForm_InsertStyle: Insert Unbind: simplify (${unbind.id})unbind-(${bind.id})unbind")
                return true to bind
            }
            is SNodeBind -> { // unbind-bind
                val commonBindings = unbind.unbindings.intersectEntries(bind.bindings)
                if( commonBindings.isNotEmpty() ) {
                    commonBindings.forEach { (k, _) ->
                        unbind.unbindings -= k
                        bind.bindings -= k
                    }
                    if (LOG.isTraceEnabled)
                        LOG.trace("SPlan2NormalForm_InsertStyle: Insert Unbind: remove (${unbind.id})unbind-(${bind.id})bind common bindings $commonBindings")
                    if( bind.bindings.isEmpty() )
                        eliminateNode(bind)
                    else bind.refreshSchema()
                    return if( unbind.unbindings.isEmpty() ) {
                        true to eliminateNode(unbind)
                    } else {
                        unbind.refreshSchema()
                        insertUnbind(unbind, true)
                    }
                }
                // the rest are unbind-bind with disjoint keys
            }
        }
        return true to unbind
    }

    private tailrec fun insertBind(bind: SNodeBind, changed: Boolean): Pair<Boolean, SNode> {
        // idea: compute a ModifyCode that is an enum and pass that below.
        val modify = checkModifyConditionsOnInputs(bind) { input ->
            input is SNodeBind ||
                    (input is SNodeUnbind &&
                            (input.unbindings.any { (p, n) -> bind.bindings[p] == n } || // common bindings
                                    input.input is SNodeAggregate || // simplify input
                                    input.input is SNodeNary ||
                                    input.input is SNodeBind ||
                                    input.input is SNodeUnbind
                                    )
                            )
        } // eliminates CSE if true
        if( !modify )
            return changed to bind
        val unbind = bind.input
        when (unbind) {
            is SNodeBind -> { // bind-bind
                unbind.bindings += bind.bindings
                unbind.refreshSchema()
                eliminateNode(bind)
                if (LOG.isTraceEnabled)
                    LOG.trace("SPlan2NormalForm_InsertStyle: Insert Bind: simplify (${bind.id})bind-(${unbind.id})bind")
                return true to unbind
            }
            is SNodeUnbind -> { // bind-unbind
                val commonBindings = bind.bindings.intersectEntries(unbind.unbindings)
                if( commonBindings.isNotEmpty() ) {
                    commonBindings.forEach { (k, _) ->
                        bind.bindings -= k
                        unbind.unbindings -= k
                    }
                    if (LOG.isTraceEnabled)
                        LOG.trace("SPlan2NormalForm_InsertStyle: Insert Bind: simplify (${bind.id})bind-(${unbind.id})unbind common bindings $commonBindings")
                    if( unbind.unbindings.isEmpty() ) eliminateNode(unbind)
                    else unbind.refreshSchema()
                    return if( bind.bindings.isEmpty() ) { true to eliminateNode(bind) }
                    else { bind.refreshSchema(); insertBind(bind, true) }
                }
                // push down bind-unbind
                val renamings = mutableMapOf<AB, AB>()
                val iter = bind.bindings.iterator()
                while (iter.hasNext()) {
                    val (dim, newName) = iter.next()
                    if (dim in unbind.unbindings) {
                        // this dim is unbound and then bound. Rename the unbound name to the bound name.
                        val oldName = unbind.unbindings.remove(dim)!!
                        iter.remove()
                        renamings += oldName to newName
                    }
                }
                if (renamings.isNotEmpty()) {
                    if (LOG.isTraceEnabled)
                        LOG.trace("SPlan2NormalForm_InsertStyle: Insert Bind: rename down (${bind.id})bind-(${unbind.id})unbind by renaming $renamings")
                    val unbindChild = unbind.inputs[0]
                    renameDownSplitCse(unbindChild, renamings, unbind)

                    // Common case: the resulting bind-unbind is empty.
                    // when would we end up with a bind-unbind that is disjoint? Never?
                    if( unbind.unbindings.isEmpty() ) eliminateNode(unbind)
                    else unbind.refreshSchema()
                    return if( bind.bindings.isEmpty() ) { true to eliminateNode(bind) }
                    else { bind.refreshSchema(); insertBind(bind, true) }
                }
            }
        }
        return true to bind
    }

    private fun renameDownSplitCse(node: SNode, renaming: Map<AB, AB>, nodeParent: SNode) {
        // nodeParent is the unbind that we rename from.
        // 2-pass strategy:
        // 1st pass gathers the node ids that are involved inside the renaming.
        // 2nd pass executes the renaming. As it does so, it splits away foreign parents not involved in the renaming.
        val seen = allNodesAtBelowToBind(nodeParent, renaming.keys)
        val bindsToRename = mutableSetOf<SNodeBind>()
        renameDownSplitCse(node, renaming, seen, bindsToRename)
        bindsToRename.forEach {
            it.bindings.mapValuesInPlace { renaming[it] ?: it }
            it.refreshSchemasUpward()
        }
    }

    private fun allNodesAtBelowToBind(node: SNode, toBound: Set<AB>): Set<Id> = mutableSetOf<Id>().also { allNodesAtBelowToBind(node, toBound, it) }

    private fun allNodesAtBelowToBind(node: SNode, toBound: Set<AB>, seen: MutableSet<Id>) {
        if( node.id in seen ) return
        seen += node.id
        if( node is SNodeBind )
            toBound.filter { it !in node.bindings.values }.toSet().let {
                if (it.isNotEmpty()) allNodesAtBelowToBind(node, it, seen)
            }
        else
            node.inputs.forEach { allNodesAtBelowToBind(it, toBound, seen) }
    }

    private fun renameDownSplitCse(node: SNode, renaming: Map<AB, AB>, seen: Set<Id>, bindsToRename: MutableSet<SNodeBind>) {
        assert(renaming.isNotEmpty())
        // if no names to be renamed in schema, then stop
//        if( node.schema.names.disjoint(renaming.keys) )
//            return
        // split CSEs from parents not inside the renaming.
        node.parents.toSet().filter { it.id !in seen }.forEach { parent ->
            splitCse(parent, node) // removes parent
        }
        // Rename
        when( node ) {
            is SNodeBind -> { // stop condition
                val newRenaming = renaming.filterKeys { it !in node.bindings.values }
//                node.bindings.mapValuesInPlace { renaming[it] ?: it }
                bindsToRename += node
                if( newRenaming.isNotEmpty() && !node.input.schema.names.disjoint(newRenaming.keys) )
                    renameDownSplitCse(node.input, newRenaming, seen, bindsToRename)
                return
            }
        }
        node.inputs.toSet().filter { !it.schema.names.disjoint(renaming.keys) }.forEach { renameDownSplitCse(it, renaming, seen, bindsToRename) }
    }

    private fun insertMult(mult: SNodeNary): Pair<Boolean, SNode> {
        val modify = checkModifyConditionsOnInputs(mult) { input ->
            input is SNodeNary && (input.op == SNodeNary.NaryOp.PLUS || input.op == SNodeNary.NaryOp.MULT) ||
                    input is SNodeAggregate && input.op == Hop.AggOp.SUM
        }
        if (!modify)
            return false to mult
        val (inPlus, inNotPlus) = mult.inputs.partition { it is SNodeNary && it.op == SNodeNary.NaryOp.PLUS }
        if( inPlus.isNotEmpty() ) {
            if (LOG.isTraceEnabled)
                LOG.trace("SPlan2NormalForm_InsertStyle: Insert * (${mult.id}): distribute into + children")
            // take Cartesian product of plus inputs. Distribute non-plus multiply inputs to plus inputs.
            inNotPlus.forEach { it.parents -= mult }
            val listOfPlusInputs = inPlus.map { p ->
                p.inputs.forEach { it.parents -= p }
                p.inputs
            }
            val newPlusInputs: List<SNodeNary> = listOfPlusInputs
                    .cartesian()
                    .map { inputsToMult: List<SNode> ->
                        SNodeNary(SNodeNary.NaryOp.MULT, inputsToMult + inNotPlus).apply { visited = true } // distribute
                    }.toList()
            val newPlus = SNodeNary(SNodeNary.NaryOp.PLUS, newPlusInputs).apply { visited = true }
            // move parents of * onto the final +
            mult.parents.forEach {
                it.inputs[it.inputs.indexOf(mult)] = newPlus
                newPlus.parents += it
            }
            newPlusInputs.forEach { insertMult(it) }
            return true to newPlus
        }
        val inAgg = mult.inputs.filter { it is SNodeAggregate && it.op == Hop.AggOp.SUM }
        if( inAgg.isNotEmpty() ) {
            if (LOG.isTraceEnabled)
                LOG.trace("SPlan2NormalForm_InsertStyle: Insert * (${mult.id}): pull Σ children above *")
            val result = rewritePullAggAboveMult.rewriteNode(mult.parents[0], mult, -1) as SPlanRewriteRule.RewriteResult.NewNode
            val topAgg = result.newNode as SNodeAggregate
            var below = topAgg.input
            while( below is SNodeAggregate && below.op == Hop.AggOp.SUM ) {
                below = below.input
            }
            below as SNodeNary
            check(below.op == SNodeNary.NaryOp.MULT)
            insertMult(below)
            insertAgg(topAgg)
            below.visited = true
            topAgg.visited = true
            return true to topAgg
        }
        if (LOG.isTraceEnabled)
            LOG.trace("SPlan2NormalForm_InsertStyle: Insert * (${mult.id}): combine into * children")
        // combine all children * into this *
        // similar to the insertPlus logic below
        val multInputs = mult.inputs.flatMap { input ->
            if (input is SNodeNary && input.op == SNodeNary.NaryOp.MULT) {
                input.inputs.forEach { it.parents -= input }
                input.inputs
            } else {
                input.parents -= mult
                listOf(input)
            }
        }
        mult.inputs.clear()
        mult.inputs += multInputs
        mult.inputs.forEach { it.parents += mult }
        return true to mult
    }

    private fun insertAgg(agg: SNodeAggregate): Pair<Boolean, SNode> {
        val modify = checkModifyConditionsOnInputs(agg) { input ->
            input is SNodeNary && input.op == SNodeNary.NaryOp.PLUS ||
                    input is SNodeAggregate && input.op == Hop.AggOp.SUM ||
                    agg.aggsNotInInputSchema().isNotEmpty()
        }
        if (!modify)
            return false to agg
        // push Σ below +, combine Σ
        val aggInput = agg.input
        if( aggInput is SNodeNary && aggInput.op == SNodeNary.NaryOp.PLUS ) {
            val plus = aggInput
            if (LOG.isTraceEnabled)
                LOG.trace("SPlan2NormalForm_InsertStyle: Insert Σ (${agg.id}): push into child +")
            // push Σ into +
            // move all parents of Σ to be parents of +
            plus.parents -= agg
            plus.parents += agg.parents
            agg.parents.forEach { it.inputs.replaceAll { if( it == agg ) plus else it } }
            agg.parents.clear()

            // first child of + gets this agg
            val plusInputs = plus.inputs.toSet().iterator()
            val piFirst = plusInputs.next()
            agg.input = piFirst
            piFirst.parents += agg
            putAggIntoPlusInput(agg, plus, piFirst)
            agg.refreshSchema()

            // remaining children get a newly constructed agg
            while( plusInputs.hasNext() ) {
                val pi = plusInputs.next()
                val newAgg = SNodeAggregate(Hop.AggOp.SUM, pi, agg.aggs).apply { visited = true }
                putAggIntoPlusInput(newAgg, plus, pi)
            }

            // check if an Σ pushed below a + now has a constant aggregation. If so, eliminate it by creating a constant *.


            plus.inputs.forEach { insertAgg(it as SNodeAggregate) }
            plus.refreshSchema()
            return true to plus
        } else if (aggInput is SNodeAggregate && aggInput.op == Hop.AggOp.SUM) {
            if (LOG.isTraceEnabled)
                LOG.trace("SPlan2NormalForm_InsertStyle: Insert Σ (${agg.id}): combine into Σ child")
            // combine Σ
            agg.aggs += aggInput.aggs
            agg.refreshSchema()
            eliminateNode(aggInput)
            if( agg.aggsNotInInputSchema().isEmpty() )
                return true to agg
        }
        val notInInput = agg.aggsNotInInputSchema()
        if( notInInput.isNotEmpty() ) {
            if (LOG.isDebugEnabled)
                LOG.debug("SPlan2NormalForm_InsertStyle: eliminate aggNames from Σ (${agg.id}) that are not in input schema: $notInInput")
            val mult = agg.input
            if( mult is SNodeNary && mult.op == SNodeNary.NaryOp.MULT ) {
                @Suppress("UNCHECKED_CAST")
                val litInputs = (agg.input.inputs.filter { it is SNodeData && it.isLiteralNumeric } as List<SNodeData>).toMutableList()

                loop@ while (notInInput.isNotEmpty() && litInputs.isNotEmpty()) {
                    for (v in 1L until (1L shl notInInput.size)) {
                        val selectSchema = notInInput.entries.filterIndexed { p, _ ->
                            v and (1L shl p) != 0L
                        }.run { Schema(this.map { (n, s) -> n to s }) }
                        val tgt = selectSchema.shapes.fold(1.0, Double::div)
                        val exact = litInputs.find {
                            val hop = it.hop as LiteralOp
                            hop.doubleValue == tgt
                        }
                        if (exact != null) {
                            // exact match with a literal - eliminate the literal
                            exact.parents -= mult
                            mult.inputs -= exact
                            agg.aggs -= selectSchema
                            notInInput -= selectSchema
                            litInputs -= exact
                            // eliminate the mult if it has a single input
                            if (mult.inputs.size == 1 && notInInput.isEmpty()) {
                                val i = mult.inputs[0]
                                i.parents -= mult
                                i.parents += agg
                                agg.input = i
                                break@loop
                            }
                            continue@loop
                        }
                    }
                    break
                }
                if (notInInput.isNotEmpty()) {
                    val mFactor = notInInput.shapes.prod()
                    val lit = SNodeData(LiteralOp(mFactor))

                    mult.inputs += lit
                    lit.parents += mult
                    agg.aggs -= notInInput
                }
            } else {
                val mFactor = notInInput.shapes.prod()
                val lit = SNodeData(LiteralOp(mFactor))
                mult.parents -= agg
                val m = SNodeNary(SNodeNary.NaryOp.MULT, mult, lit)
                m.parents += agg
                agg.input = m
                agg.aggs -= notInInput
            }
            if( agg.aggs.isEmpty() ) {
                return true to eliminateNode(agg)
            }
        }

        return true to agg
    }

    private fun putAggIntoPlusInput(agg: SNodeAggregate, plus: SNodeNary, pi: SNode) {
        // agg.input = pi; pi.parents += agg
        plus.inputs.mapInPlace {
            if( it == pi ) {
                pi.parents -= plus
                agg.parents += plus
                agg
            } else it
        }
    }

    private fun insertPlus(plus: SNodeNary): Pair<Boolean, SNode> {
        // put all +s together among the inputs
        val modify = checkModifyConditionsOnInputs(plus) { input ->
            input is SNodeNary && input.op == SNodeNary.NaryOp.PLUS
        }
        if (!modify)
            return false to plus
        if (LOG.isTraceEnabled)
            LOG.trace("SPlan2NormalForm_InsertStyle: Insert + (${plus.id}): combine into + children")
        val plusInputs = plus.inputs.flatMap { input ->
            if (input is SNodeNary && input.op == SNodeNary.NaryOp.PLUS) {
                input.inputs.forEach { it.parents -= input }
                input.inputs
            } else {
                input.parents -= plus
                listOf(input)
            }
        }
        plus.inputs.clear()
        plus.inputs += plusInputs
        plus.inputs.forEach { it.parents += plus }
        return true to plus
    }

    private inline fun checkModifyConditionsOnInputs(parent: SNode, modifyCond: (SNode) -> Boolean): Boolean {
        return parent.inputs.toSet().fold(false) { acc, input ->
            if (modifyCond(input)) {
                if (!input.parents.all { it == parent })
                    splitCse(parent, input)
                true
            } else acc
        }
    }

    /**
     * Create a copy of [input] that has exactly one parent: [parent].
     * [parent] is removed from the original [input]'s parents.
     * Return the copy.
     */
    fun <N : SNode> splitCse(parent: SNode, input: N): N {
        // split CSE
        val copy = input.shallowCopyNoParentsYesInputs()
        parent.inputs.mapInPlace {
            if (it == input) {
                input.parents -= parent
                copy.parents += parent
                copy
            } else it
        }
        return copy
    }
}




package org.apache.sysml.hops.spoof2

import org.apache.sysml.hops.Hop
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
    private const val CHECK_DURING_RECUSION = false
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
            val result = toNormalForm(root, roots)
            changed = result || changed
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
                LOG.trace("'SPlan2NormalForm_InsertStyle' rewrites yield: " + Explain.explainSPlan(roots))
            return SPlanRewriter.RewriterResult.NewRoots(roots)
        }
    }

    /**
     *
     */
    private fun toNormalForm(node: SNode, allRoots: List<SNode>): Boolean {
//        // wait until all children processed
//        if( !node.inputs.all { it.id in resultMap } )
//            return false
        if (node.visited)
            return false
        var changed = node.inputs.toSet().fold(false) { acc, input -> toNormalForm(input, allRoots) || acc }
        // inductive hypothesis: each input is in normal form

        // Split input CSEs only if we would modify them. Otherwise allow inputs to have multiple parents.
        val newChanged = when (node) {
            is SNodeNary -> {
                if (node.op == SNodeNary.NaryOp.PLUS) {
                    insertPlus(node)
                } else if (node.op == SNodeNary.NaryOp.MULT) {
                    insertMult(node)
                } else false
            }
            is SNodeAggregate -> {
                if (node.op == Hop.AggOp.SUM)
                    insertAgg(node)
                else false
            }
            is SNodeBind -> {
                if (node.bindings.isEmpty()) {
                    eliminateNode(node)
                    true
                } else insertBind(node)
            }
            is SNodeUnbind -> {
                if (node.unbindings.isEmpty()) {
                    eliminateNode(node)
                    true
                } else insertUnbind(node)
            }
            else -> false
        }
        node.visited = true

        if (CHECK_DURING_RECUSION && newChanged)
            SPlanValidator.validateSPlan(allRoots, false)
        if (EXPLAIN_DURING_RECURSION && LOG.isTraceEnabled && newChanged)
            LOG.trace(Explain.explainSPlan(allRoots, true))

        return changed || newChanged
    }

    private tailrec fun insertUnbind(unbind: SNodeUnbind): Boolean {
        val modify = checkModifyConditionsOnInputs(unbind) { input ->
            input is SNodeUnbind ||
                    (input is SNodeBind && !input.bindings.keys.disjoint(unbind.unbindings.keys))
        }
        if( !modify )
            return false
        val bind = unbind.input
        when (bind) {
            is SNodeUnbind -> { // unbind-unbind
                bind.unbindings += unbind.unbindings
                bind.refreshSchema()
                eliminateNode(unbind)
                if (LOG.isTraceEnabled)
                    LOG.trace("SPlan2NormalForm_InsertStyle: Insert Unbind: simplify (${unbind.id})unbind-(${bind.id})unbind")
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
                        eliminateNode(unbind)
                        true
                    } else {
                        unbind.refreshSchema()
                        insertUnbind(unbind)
                    }
                }
                // the rest are unbind-bind with disjoint keys
            }
        }
        return true
    }

    private tailrec fun insertBind(bind: SNodeBind): Boolean {
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
            return false
        val unbind = bind.input
        when (unbind) {
            is SNodeBind -> { // bind-bind
                unbind.bindings += bind.bindings
                unbind.refreshSchema()
                eliminateNode(bind)
                if (LOG.isTraceEnabled)
                    LOG.trace("SPlan2NormalForm_InsertStyle: Insert Bind: simplify (${bind.id})bind-(${unbind.id})bind")
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
                    return if( bind.bindings.isEmpty() ) { eliminateNode(bind); true }
                    else { bind.refreshSchema(); insertBind(bind) }
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
                    return if( bind.bindings.isEmpty() ) { eliminateNode(bind); true }
                    else { bind.refreshSchema(); insertBind(bind) }
                }
            }
        }
        return true
    }

    private fun renameDownSplitCse(node: SNode, renaming: Map<AB, AB>, nodeParent: SNode) {
        // nodeParent is the unbind that we rename from.
        // 2-pass strategy:
        // 1st pass gathers the node ids that are involved inside the renaming.
        // 2nd pass executes the renaming. As it does so, it splits away foreign parents not involved in the renaming.
        val seen = allNodesAtBelowToBind(nodeParent, renaming.keys)
        renameDownSplitCse(node, renaming, seen)
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

    private fun renameDownSplitCse(node: SNode, renaming: Map<AB, AB>, seen: Set<Id>) {
        assert(renaming.isNotEmpty())
        // split CSEs from parents not inside the renaming.
        node.parents.toSet().filter { it.id !in seen }.forEach { parent ->
            splitCse(parent, node) // removes parent
        }
        // Rename
        when( node ) {
//            is SNodeAggregate -> node.aggs.replaceKeys { renaming[it] ?: it }
            is SNodeBind -> { // stop condition
                node.bindings.mapValuesInPlace { renaming[it] ?: it }
                val newRenaming = renaming.filterKeys { it !in node.bindings.values }
                if( newRenaming.isNotEmpty() )
                    renameDownSplitCse(node.input, newRenaming, seen)
                node.refreshSchema()
                return
            }
        }
        node.inputs.forEach { renameDownSplitCse(it, renaming, seen) }
        node.refreshSchema()
    }

    private fun insertMult(mult: SNodeNary): Boolean {
        val modify = checkModifyConditionsOnInputs(mult) { input ->
            input is SNodeNary && (input.op == SNodeNary.NaryOp.PLUS || input.op == SNodeNary.NaryOp.MULT) ||
                    input is SNodeAggregate && input.op == Hop.AggOp.SUM
        }
        if (!modify)
            return false
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
            return true
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
            return true
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
        return true
    }

    private fun insertAgg(agg: SNodeAggregate): Boolean {
        val modify = checkModifyConditionsOnInputs(agg) { input ->
            input is SNodeNary && input.op == SNodeNary.NaryOp.PLUS ||
                    input is SNodeAggregate && input.op == Hop.AggOp.SUM
        }
        if (!modify)
            return false
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

            plus.inputs.forEach { insertAgg(it as SNodeAggregate) }
            plus.refreshSchema()
        } else if (aggInput is SNodeAggregate && aggInput.op == Hop.AggOp.SUM) {
            if (LOG.isTraceEnabled)
                LOG.trace("SPlan2NormalForm_InsertStyle: Insert Σ (${agg.id}): combine into Σ child")
            // combine Σ
            agg.aggs += aggInput.aggs
            agg.refreshSchema()
            eliminateNode(aggInput)
        }
        return true
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

    private fun insertPlus(plus: SNodeNary): Boolean {
        // put all +s together among the inputs
        val modify = checkModifyConditionsOnInputs(plus) { input ->
            input is SNodeNary && input.op == SNodeNary.NaryOp.PLUS
        }
        if (!modify)
            return false
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
        return true
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

    private fun splitCse(parent: SNode, input: SNode) {
        // split CSE
        val copy = input.deepCopy()
        parent.inputs.mapInPlace {
            if (it == input) {
                input.parents -= parent
                copy.parents += parent
                copy
            } else it
        }
    }


}




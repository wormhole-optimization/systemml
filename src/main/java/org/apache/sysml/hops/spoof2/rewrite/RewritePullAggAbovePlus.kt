package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.Hop.AggOp
import org.apache.sysml.hops.LiteralOp
import org.apache.sysml.hops.spoof2.plan.*
import org.apache.sysml.hops.spoof2.plan.SNodeNary.NaryOp

/**
 * First pass: if `a` is in the schema of +,
 * change `* + <- a`
 * to `+ <- Bind[a'] <- Unbind[a ] <- a`.
 *
 * Pattern:
 * Assumes `a` and `b` are not in the schema of +.
 * ```
 *      \ /     ->           \ /
 *       +      ->            Σa
 *    // | \ \  ->            |
 *F  Σa Σa Σb D ->            +
 * \ /   | |    ->       //   |  \      \
 *  A    B C    -> F    *     *   *      *
 *              ->  \ / |    / |  | \    | \
 *              ->   A /|b| B /|b|C /|a| D /|a|/|b|
 * ```
 *
 * RewriteSplitCSE handles foreign parents on the Σs.
 */
class RewritePullAggAbovePlus : SPlanRewriteRule() {

    override fun rewriteNode(parent: SNode, node: SNode, inputPosition: Int): RewriteResult {
        if( node !is SNodeNary || node.op != NaryOp.PLUS )
            return RewriteResult.NoChange
        val plus: SNodeNary = node

        val mapInputToNames: MutableMap<Name, Shape> = mutableMapOf()
        // for each input that is an SNodeAggregate,
        //  add the aggNames to the map and do the unbind-bind rename on its input if the name is in the schema of +
        //  then kill the SNodeAggregate
        plus.inputs.toSet().forEach { pc ->
            if( pc is SNodeAggregate && pc.op == AggOp.SUM // todo expand to min, max
                    && pc.parents.all { it == plus }) {
                // assume the agg is not empty
                val overlapNames = pc.aggs.names.withIndex().filter { (_, n) -> n in plus.schema }.map { (i,n) -> i to n }.toMap()
                if( overlapNames.isNotEmpty() ) {
                    pc.input.parents -= pc
                    val u = SNodeUnbind(pc.input, overlapNames)
                    val nb = overlapNames.mapValues { (_,n) -> Schema.freshNameCopy(n) }
                    val b = SNodeBind(u, nb)
                    b.parents += pc
                    pc.input = b
                    pc.aggs.names.mapInPlaceIndexed { i, n -> if( i in nb ) nb[i]!! else n }
                    if( LOG.isTraceEnabled )
                        LOG.trace("In RewritePullAggAbovePlus, rename (${pc.id}) $overlapNames into ${pc.aggs}")
                }
                // kill pc
                mapInputToNames += pc.aggs.zip().toMap()
                pc.input.parents -= pc
                val cnt = pc.parents.size
                for( i in 1..cnt ) {
                    pc.input.parents += plus
                    plus.inputs[plus.inputs.indexOf(pc)] = pc.input
                }
            }
        }
        if( mapInputToNames.isNotEmpty() ) {
            val allAggNames: Map<Name,Shape> = mapInputToNames

            // for each input, for each aggName, if the aggName is not in its schema, divide the input by the aggName's shape.
            plus.inputs.toSet().forEach { pc ->
                val notInSchema = allAggNames.filter { (n, _) -> n !in pc.schema }
                if (notInSchema.isNotEmpty()) {
                    val divide = notInSchema.values.fold(1.0, Double::div)
                    val lit = SNodeData(LiteralOp(divide))

                    val cnt = pc.parents.count { it == plus }
                    pc.parents.removeIf { it == plus }
                    val mult = SNodeNary(NaryOp.MULT, pc, lit)
                    repeat(cnt) { mult.parents += plus }
                    plus.inputs.mapInPlace { if (it == pc) mult else it }
                }
            }
            plus.refreshSchema()

            // create an SNodeAggregate above + with all the names
            val parents = ArrayList(plus.parents)
            plus.parents.clear()
            val allAgg = SNodeAggregate(AggOp.SUM, plus, Schema(allAggNames))
            allAgg.parents += parents
            parents.forEach { it.inputs[it.inputs.indexOf(plus)] = allAgg }

            if( LOG.isTraceEnabled )
                LOG.trace("RewritePullAggAbovePlus: pull ${mapInputToNames.size} agg nodes w/ names $allAggNames above (${plus.id}) $plus")
            return RewriteResult.NewNode(allAgg)
        }
        return RewriteResult.NoChange
    }
}

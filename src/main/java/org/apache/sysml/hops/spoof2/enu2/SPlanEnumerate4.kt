package org.apache.sysml.hops.spoof2.enu2

import org.apache.sysml.hops.spoof2.Spoof2Compiler
import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.rewrite.SPlanTopDownRewriter
import org.apache.sysml.utils.Explain

class SPlanEnumerate4(initialRoots: Collection<SNode>) {
    constructor(vararg inputs: SNode) : this(inputs.asList())
    private val _origRoots = initialRoots.toList()
    private val _preRules = listOf(
            RewriteMultPlusToNotNot
    )
    private val _postRules = listOf(
            RewriteNotNotElim
    )

    fun execute() {
        SPlanTopDownRewriter.rewriteDown(_origRoots, _preRules)

        val dogbs = DagOfGraphBag.form(_origRoots)

        if (Spoof2Compiler.LOG.isTraceEnabled) {
            Spoof2Compiler.LOG.trace("dogbs before connected components: \n\t${dogbs.graphBags.joinToString("\n\t") { g -> "$g"}}")
        }

        val resultNodes = Array<SNode?>(dogbs.graphBags.size) {null}
        for (cc in dogbs.decomposeByConnectedComponents()) {
            val nodes = BottomUpOptimize(cc).drive()
            cc.origIndices.zip(nodes).forEach { (i, n) ->
                resultNodes[i] = n
            }
        }

        // Connect new nodes to parents in exactly the original order.
        for ((gbi, _bc) in resultNodes.withIndex()) { // == bestComplete.indices
            val bc = _bc!!

            val pa = dogbs.graphBagParents[gbi]
            val paIdx = dogbs.graphBagParentInputIndices[gbi]

            for (idx in pa.indices) {
                val p = pa[idx]
                val i = paIdx[idx]

                p.inputs.add(i, bc) // Orientation is okay?
                bc.parents.add(p)
            }
        }

        SPlanTopDownRewriter.rewriteDown(_origRoots, _postRules)

        if( Spoof2Compiler.LOG.isTraceEnabled )
            Spoof2Compiler.LOG.trace("After SPlanEnumerate4: "+ Explain.explainSPlan(_origRoots))
    }
}

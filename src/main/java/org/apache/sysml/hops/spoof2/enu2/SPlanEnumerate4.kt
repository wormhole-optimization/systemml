package org.apache.sysml.hops.spoof2.enu2

import org.apache.commons.logging.LogFactory
import org.apache.sysml.hops.spoof2.Spoof2Compiler
import org.apache.sysml.hops.spoof2.plan.SNode

class SPlanEnumerate4(initialRoots: Collection<SNode>) {
    constructor(vararg inputs: SNode) : this(inputs.asList())
    private val _origRoots = initialRoots.toList()

    fun execute() {
        val dogbs = DagOfGraphBags.form(_origRoots)

        if (Spoof2Compiler.LOG.isTraceEnabled) {
            Spoof2Compiler.LOG.trace("dogbs before connected components: \n\t${dogbs.graphBags.joinToString("\n\t") { g -> "$g"}}")
        }

        for (cc in dogbs.decomposeByConnectedComponents()) {
            BottomUpOptimize(cc).drive()
        }
    }
}
package org.apache.sysml.test.unit

import org.apache.sysml.hops.Hop
import org.apache.sysml.hops.OptimizerUtils
import org.apache.sysml.utils.Explain
import org.apache.sysml.utils.ParseExplain
import org.junit.Assume
import org.junit.Test
import java.io.File

class ParseExplainTest {

    init {
        OptimizerUtils.resetDefaultSize()
    }

    @Test
    fun testParseExplain() {
        val explain = listOf(
                "--(441) TRead P [10000,2,1000,1000,200]MD [0,0,153 -> 153MB], CP",
                "--(446) rix (441,[1],[10],[1],[1]) [10000000,1,1000,1000,-1]MD [153,0,76 -> 229MB], CP",
                "--(1437) u(sprop) (446) [10000,1,1000,1000,-1]MD [76,0,76 -> 153MB], CP"
        )
        val hops = ParseExplain.explainToHopDag(explain)
        println(Explain.explainHops(hops))

        val dot = Explain.hop2dot(hops)
        println(dot)
    }

//    /**
//     * Read in Explain input for one Hop Dag from `explain.txt` into a DOT file, saved at `dot.dot`.
//     */
//    @Test
//    fun testLiveInput() {
//        val pres = listOf("explain-als-cg-mod-best.txt")
//        ParseExplain.main(pres.toTypedArray())
//    }
}
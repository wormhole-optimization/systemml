package org.apache.sysml.test.unit

import org.apache.sysml.utils.Explain
import org.apache.sysml.utils.ParseExplain
import org.junit.Test

class ParseExplainTest {

    @Test
    fun testParseExplain() {
        val explain = listOf(
                "--(441) TRead P [10000,2,1000,1000,200]MD [0,0,153 -> 153MB], CP",
                "--(446) rix (441,[1],[10],[1],[1]) [10000000,1,1000,1000,-1]MD [153,0,76 -> 229MB], CP",
                "--(1437) u(sprop) (446) [10000,1,1000,1000,-1]MD [76,0,76 -> 153MB], CP"
        )
        val hops = ParseExplain.explainToHopDag(explain)
        println(Explain.explainHops(hops))
    }
}
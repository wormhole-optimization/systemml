package org.apache.sysml.test.unit

import org.apache.sysml.utils.Explain
import org.apache.sysml.utils.Explain.getHopDAG
import org.apache.sysml.utils.ParseExplain
import org.junit.Assume
import org.junit.Test
import java.io.File

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

//        val statement = OutputStatement()
//        val sb = StatementBlock()
//        sb.addStatement()
//        val dml = DMLProgram()
//        dml.statementBlocks.add(sb)

        val nodes = StringBuilder()
        val sb = StringBuilder()
        sb.append("digraph {\n")
        for (hop in hops)
            sb.append(getHopDAG(hop, nodes, arrayListOf(), false))
        sb.append(nodes)
        sb.append("rankdir = \"BT\"\n")
        sb.append("}\n")

        println(sb)
    }

    @Test
    fun testLiveInput() {
        val f = File("explain.txt")
        if( !f.exists() ) {
            Assume.assumeTrue("Please place the Explain output you wish to recover into ${f.absolutePath}", false)
        }
        val lines = f.readLines()
        val hops = ParseExplain.explainToHopDag(lines)
        println(Explain.explainHops(hops))

        val nodes = StringBuilder()
        val sb = StringBuilder()
        sb.append("digraph {\n")
        for (hop in hops)
            sb.append(getHopDAG(hop, nodes, arrayListOf(), false))
        sb.append(nodes)
        sb.append("rankdir = \"BT\"\n")
        sb.append("}\n")

        println(sb)
    }
}
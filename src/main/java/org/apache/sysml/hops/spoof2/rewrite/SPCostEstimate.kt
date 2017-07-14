package org.apache.sysml.hops.spoof2.rewrite

import org.apache.sysml.hops.spoof2.plan.Name
import org.apache.sysml.hops.spoof2.plan.Schema

object SPCostEstimate {

    /**
     * Number of multiplication operations for multiplying these two tensors.
     * The result has the union of dimensions of the inputs.
     * The number of multiplications is the product of the sizes of the schemas in the output, counted once each.
     * todo: sparsity
     */
    private fun numMultiply(a: Schema, b: Schema): Long {
        val ns = Schema(a).apply {unionWithBound(b)}
        return ns.shapes.reduce(Long::times)
    }
    // when there are more than two tensors to multiply, the order can be significant.
    // ex: A * b * c. A is matrix; b and c are vector.
    // Multiply b and c first, then A, to get the smallest number of multiplications.

    private fun numAdd(elimName: Name, a: Schema): Long {
        if( elimName !in a )
            return 0L
        var adds = 1L
        for (i in a.indices) {
            adds *= if( a.names[i] == elimName )
                a.shapes[i]-1
            else
                a.shapes[i]
        }
        return adds
    }

}
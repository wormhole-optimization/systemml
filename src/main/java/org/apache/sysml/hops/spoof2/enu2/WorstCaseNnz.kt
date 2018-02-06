package org.apache.sysml.hops.spoof2.enu2

import org.apache.sysml.hops.spoof2.plan.*

/**
 * Pass in a memo map, that will be updated with the nnz estimates not already memoized.
 *
 * Σ nodes followed by a * (matrix-multiply-like) will have their nnz estimated with a better formula.
 * OR nodes get the nnz estimate of their first child.
 * All nodes receive an nnz estimate.
 */
object WorstCaseNnz : NnzInferer {

    /**
     * Worst case estimate, assumes nz divided evenly among output cells:
     * `s = min(1, nnz/Π_{shapes-in-output})`.
     */
    override fun inferAgg(d: Map<Name,Shape>, cz: Nnz, cd: Map<Name,Shape>): Nnz {
        return minOf(d.values.prod(), cz)
    }

    /**
     * Worst case estimate, assumes nz divided evenly among output cells:
     * `s = Π_{*-inputs} min(1, nnz/Π_{shapes-in-output})`.  ((Matrix multiply))
     */
    override fun inferMatrixMult(d: Map<Name, Shape>, cz: List<Nnz>, cd: List<Map<Name, Shape>>): Nnz {
        val s = cz.zip(cd).map { (czi, cdi) ->
            minOf(1.0, czi.toDouble() / cdi.filter { (n,_) -> n in d }.values.prod())
        }.prod()
        return (s * d.values.prod()).toLong()
    }

    /**
     * Worst case estimates, assumes nz overlap completely.
     * *: min of sparsities.
     */
    override fun inferMult(d: Map<Name, Shape>, cz: List<Nnz>, cd: List<Map<Name, Shape>>): Nnz {
        val s = NnzInferer.childSparities(cz, cd).min()!!
        return (s * d.values.prod()).toLong()
    }

    /**
     * Worst case estimates, assumes nz overlap completely.
     * +: min(1, sum of sparsities).
     */
    override fun inferAdd(d: Map<Name, Shape>, cz: List<Nnz>, cd: List<Map<Name, Shape>>): Nnz {
        val s = minOf(1.0, NnzInferer.childSparities(cz, cd).sum())
        return (s * d.values.prod()).toLong()
    }

}
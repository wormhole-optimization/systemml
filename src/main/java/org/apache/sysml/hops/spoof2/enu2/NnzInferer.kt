package org.apache.sysml.hops.spoof2.enu2

import org.apache.sysml.hops.spoof2.plan.*

interface NnzInferer {
    /** Infer the nnz of a *.
     * Child `i`'s sparsity is `cz\[i\] / cd\[i\].prod()`.
     * @param d The dense shapes of the result.
     * @param cz The nnz of children.
     * @param cd The dense shapes of children.
     */
    fun inferMult(d: Map<Name,Shape>, cz: List<Nnz>, cd: List<Map<Name,Shape>>): Nnz
    /** Infer the nnz of a +.
     * Child `i`'s sparsity is `cz\[i\] / cd\[i\].prod()`.
     * @param d The dense shapes of the result.
     * @param cz The nnz of children.
     * @param cd The dense shapes of children.
     */
    fun inferAdd(d: Map<Name,Shape>, cz: List<Nnz>, cd: List<Map<Name,Shape>>): Nnz
    /** Infer the nnz of a Σ.
     * Child's sparsity is `cz / cd.prod()`.
     * @param d The dense shapes of the result, after Σ. Empty list if full aggregation.
     * @param cz The nnz of the child.
     * @param cd The dense shapes of the child.
     */
    fun inferAgg(d: Map<Name,Shape>, cz: Nnz, cd: Map<Name,Shape>): Nnz
    /** Infer the nnz of a Σ-* that is a matrix multiply. Children are that of the *.
     * Child `i`'s sparsity is `cz\[i\] / cd\[i\].prod()`.
     * @param d The dense shapes of the result.
     * @param cz The nnz of children.
     * @param cd The dense shapes of children.
     */
    fun inferMatrixMult(d: Map<Name,Shape>, cz: List<Nnz>, cd: List<Map<Name,Shape>>): Nnz {
        // Default implementation:
        val md = cd.reduce { a, b -> a+b }
        val mz = inferMult(md, cz, cd)
        return inferAgg(d, mz, md)
    }

    companion object {
        fun childSparities(cz: List<Nnz>, cd: List<Map<Name, Shape>>): List<Double> {
            return cz.zip(cd).map { (czi, cdi) ->
                czi.toDouble() / cdi.values.prod()
            }
        }
    }

}
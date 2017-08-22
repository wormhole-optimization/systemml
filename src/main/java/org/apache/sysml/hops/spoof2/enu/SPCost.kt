package org.apache.sysml.hops.spoof2.enu

import org.apache.sysml.hops.spoof2.plan.Name
import org.apache.sysml.hops.spoof2.plan.Schema
import org.apache.sysml.hops.spoof2.plan.sumByLong

data class SPCost(
        val nMultiply: Long = 0L,
        val nAdd: Long = 0L
//        val nUnknownENode: List<ENode> = emptyList()
) : Comparable<SPCost> {
    override fun compareTo(other: SPCost): Int {
        // todo consider memory - check if below distributed threshold
        return (nMultiply + nAdd - other.nMultiply - other.nAdd ).toInt()
    }

    operator fun plus(c: SPCost) = if( c == SPCost.ZERO_COST ) this else SPCost(this.nMultiply + c.nMultiply, this.nAdd + c.nAdd)
    fun plusMultiply(m: Long) = if(m == 0L) this else SPCost(nMultiply + m, nAdd) //, nUnknownENode)
    fun plusAdd(m: Long) = if(m == 0L) this else SPCost(nMultiply, nAdd + m) //, nUnknownENode)
    fun min(c: SPCost) = if( this <= c ) this else c
    fun max(c: SPCost) = if( this >= c ) this else c
    operator fun minus(c: SPCost) = if(c == ZERO_COST) this else SPCost(this.nMultiply - c.nMultiply, this.nAdd - c.nAdd)
    operator fun unaryMinus() = if(this == ZERO_COST) this else SPCost(-this.nMultiply, -this.nAdd)
    fun addPart() = if(nMultiply == 0L) this else SPCost(0, nAdd)
    fun multiplyPart() = if(nAdd == 0L) this else SPCost(nMultiply, 0)
    override fun toString() = "cost($nMultiply, $nAdd)"

    companion object {
        val MAX_COST = SPCost(Long.MAX_VALUE, Long.MAX_VALUE)
        val ZERO_COST = SPCost(0, 0)

        /**
         * Number of multiplication operations for multiplying these two tensors.
         * The result has the union of dimensions of the inputs.
         * The number of multiplications is the product of the sizes of the schemas in the output, counted once each.
         * todo: sparsity
         */
        private fun numMultiply(a: Schema, b: Schema): Long {
            val ns = Schema(a).apply { unionWithBound(b) }
            return ns.shapes.reduce(Long::times)
        }
        // when there are more than two tensors to multiply, the order can be significant.
        // ex: A * b * c. A is matrix; b and c are vector.
        // Multiply b and c first, then A, to get the smallest number of multiplications.

        private fun numAdd(elimName: Name, a: Schema): Long {
            if (elimName !in a)
                return 0L
            var adds = 1L
            for (i in a.indices) {
                adds *= if (a.names[i] == elimName)
                    a.shapes[i] - 1
                else
                    a.shapes[i]
            }
            return adds
        }

        /**
         * Decision on whether to multiply a vector with one matrix or another,
         * when there is a choice for vector expansion multiply to multiply on either side.
         */
        fun betterToMultiplyWithFirst(vector: Schema, matrix1: Schema, matrix2: Schema): Boolean {
            require(vector.names.size == 1
                    && vector.names[0] in matrix1 && vector.names[0] in matrix2
                    && matrix1.size == 2 && matrix2.size == 2
            ) { "vector $vector matrix1 $matrix1 matrix2 $matrix2" }
            val vname = vector.names[0]
            val i1 = matrix1.names.indexOfFirst { it != vname }
            val i2 = matrix2.names.indexOfFirst { it != vname }
            return matrix1.shapes[i1] <= matrix2.shapes[i2]
        }

        fun costFactoredBlock(spb: SumProduct, recursive: Boolean = true): SPCost {
            return when( spb ) {
                is SumProduct.Input -> ZERO_COST
                is SumProduct.Block -> {
                    val recCost =
                            if(recursive) spb.edges.fold(ZERO_COST) { acc, edge -> acc + costFactoredBlock(edge, recursive) }
                            else SPCost.ZERO_COST

                    recCost + when( spb.allSchema().size ) {
                        0 -> ZERO_COST
                        1 -> { // all edges are vectors over this single name
                            val isAgg = spb.aggNames().isNotEmpty()
                            val shape = spb.allSchema().shapes[0]
                            // first multiply them together
                            val multCost = (spb.edges.size-1) * shape
                            val addCost = if( isAgg ) shape - 1 else 0L
                            SPCost(multCost, addCost)
                        }
                        2 -> { // a--b: vectors on a; matrices on a,b; vectors on b
                            // first multiply the groups together
                            val repSchemasToCount = spb.edgesGroupByIncidentNames().map { (_,edges) -> edges.first().schema to edges.size }
                            val multWithinGroupCost = repSchemasToCount.sumByLong { (repSchema,count) ->
                                (count-1) * repSchema.shapes.fold(1L) { acc, shape -> acc * shape }
                            }
                            // now multiply across groups
                            val allSchema = spb.allSchema() //repSchemasToCount.map(Pair<Schema,Int>::first).fold(Schema()) { acc, schema -> acc.apply { unionWithBound(schema) } }
                            val tmp = allSchema.zip()
                            var (n1,s1) = tmp.first()
                            var (n2,s2) = tmp.drop(1).first()
                            var h1 = spb.edgesGroupByIncidentNames()[setOf(n1)] != null
                            var h2 = spb.edgesGroupByIncidentNames()[setOf(n2)] != null
                            val h12 = spb.edgesGroupByIncidentNames()[setOf(n1, n2)] != null
                            var a1 = n1 in spb.aggNames()
                            var a2 = n2 in spb.aggNames()
                            if( !h1 && h2 ) { // symmetry
                                h1 = true; h2 = false
                                run { val t = n1; n1 = n2; n2 = t }
                                run { val t = s1; s1 = s2; s2 = t }
                                run { val t = a1; a1 = a2; a2 = t }
                            }
//                            check(h12) {"SumProduct not completely factored; can be partitioned into disjoint vectors; $spb"}

                            val costCrossGroup = if( !h12 ) {
                                check( !a1 && !a2 ) {"SumProduct not completely factored; can be partitioned into disjoint vectors; $spb"}
                                if( h1 && h2 )
                                    SPCost(s1 * s2, 0) // outer product
                                else
                                    ZERO_COST
                            }
                            else
                            if( h1 ) {
                                if( h2 ) {
                                    if( a1 )
                                        if( a2 ) SPCost(s1 * s2 + s1, s1 * (s2 - 1) + s1 - 1).min(SPCost(s1 * s2 + s2, (s1 - 1) * s2 + s2 - 1))
                                        else SPCost(s1 * s2 + s2, (s1 - 1) * s2)
                                    else
                                        if( a2 ) SPCost(s1 * s2 + s1, s1 * (s2 - 1))
                                        else SPCost(2 * s1 * s2, 0)
                                } else {
                                    if( a1 )
                                        if( a2 ) SPCost(s1, s1 * (s2 - 1) + s1 - 1)
                                        else SPCost(s1 * s2, (s1 - 1) * s2)
                                    else
                                        if( a2 ) SPCost(s1, s1 * (s2 - 1))
                                        else SPCost(s1 * s2, 0)
                                }
                            } else {
                                assert(!h2)
                                // only h12; no cross-group multiply
                                ZERO_COST
                            }
                            costCrossGroup.plusMultiply(multWithinGroupCost)
                        }
                        3 -> {
                            check( spb.aggNames().isNotEmpty() ) {"SumProduct not completely factored; output is a tensor from $spb"}
                            //We could be

                            // The only possible pattern is a--x--y with matrix Aax, matrix Bxy, and possibly vector Vx
                            // If the vector Vx is present, then either multiply it with A or with B.

                            // first multiply the groups together (not necessary if fully factored, but why not)
                            val repSchemasToCount = spb.edgesGroupByIncidentNames().map { (_,edges) -> edges.first().schema to edges.size }
                            check( repSchemasToCount.size <= 3 ) {"SumProduct not completely factored; more than 3 groups of edges in $spb"}
                            val multWithinGroupCost = repSchemasToCount.sumByLong { (repSchema,count) ->
                                (count-1) * repSchema.shapes.reduce(Long::times)
                            }

                            var vSchema: Schema? = null
                            var _m1Schema: Schema? = null
                            var _m2Schema: Schema? = null
                            repSchemasToCount.forEach { (schema,_) ->
                                if( schema.size == 1 ) {
                                    check( vSchema == null ) {"SumProduct not completely factored; saw vectors twice in $spb"}
                                    vSchema = schema
                                }
                                else if( _m1Schema == null )
                                    _m1Schema = schema
                                else {
                                    check( _m2Schema == null ) {"saw too many groups of matrices in $spb"}
                                    _m2Schema = schema
                                }
                            }
                            check(_m1Schema != null && _m2Schema != null) {"expected two kinds of matrices in $spb"}
                            val m1Schema = _m1Schema!!
                            val m2Schema = _m2Schema!!
                            val n12 = m1Schema.names.intersect(m2Schema.names).also { check(it.size == 1) {"the matrices' schemas should only overlap in one position"} }.first()
                            val s12 = m1Schema.getShape(n12)
                            val n1 = (m1Schema.names - n12).first()
                            val n2 = (m2Schema.names - n12).first()
                            val s1 = (m1Schema.shapes - s12).first()
                            val s2 = (m2Schema.shapes - s12).first()
                            check( n1 !in spb.aggNames() && n2 !in spb.aggNames() && n12 in spb.aggNames() ) {"unexpected aggregation pattern in $spb"}

                            val vectorMultCost = if( vSchema != null ) {
                                check( vSchema!!.names.first() == n12 ) {"SumProduct not completely factored; vector is not over shared dimension in $spb"}
                                Math.min(s1, s2) * s12
                            } else 0L
                            val matrixMultCost = SPCost(s1 * s12 * s2, s1 * (s12 - 1) * s2)

                            matrixMultCost.plusMultiply(multWithinGroupCost + vectorMultCost)
                        }
                        else -> throw IllegalStateException("SumProduct not completely factored; found block with more than two names $spb")
                    }
                }
            }
        }
    }

}
package org.apache.sysml.hops.spoof2.plan

import org.apache.sysml.hops.HopsException
import org.apache.sysml.hops.spoof2.enu.EPath
import org.apache.sysml.hops.spoof2.enu.SPCost
import java.util.ArrayList

import org.apache.sysml.runtime.controlprogram.parfor.util.IDSequence

// consider making this a Sealed class
abstract class SNode(inputs: List<SNode>) {

    //globally unique SNode id
    val id: Id = _idSeq.nextID
    val parents: ArrayList<SNode> = ArrayList()
    val inputs: ArrayList<SNode> = ArrayList(inputs)
    var visited: Boolean = false

    // dimensions and names on dimensions
    val schema = Schema() // initial schema is uncomputed

    /** Set the [schema] as a function of this SNode's type and inputs.
     * Call this to recompute after changing the node's inputs. */
    abstract fun refreshSchema()




    constructor(vararg inputs: SNode) : this(inputs.asList())
    init {
        for (input in inputs) {
            @Suppress("LeakingThis")
            input.parents.add(this)
        }
    }

    fun resetVisited() {
        if (!visited)
            return
        visited = false
        for (c in inputs)
            c.resetVisited()
    }

    abstract override fun toString(): String

    /**
     * Check whether this SNode has a correct number of inputs. Some ops only allow a single input (transpose, exp)
     * while others allow any number of inputs (mult).
     *
     * @throws HopsException if this SNode has an illegal number of inputs (a kind of Illegal State)
     */
    @Throws(HopsException::class)
    abstract fun checkArity()

    inline fun check(condition: Boolean, message: () -> String) {
        SNodeException.check(condition, this, message)
    }
    fun checkLabels() {
        // no label can appear more than once in an input
        this.check( schema.names.size == schema.names.distinct().size ) {"a label appears more than once in $schema"}
        // only these cases may have unbound attributes
        this.check( this is SNodeBind ||
                this is SNodeUnbind ||
                this is SNodeData ||
                this is SNodeExt ||
                schema.allBound() )
        {"has unbound attributes but is not a LeftIndex or RightIndex"}
    }

    companion object {
        private val _idSeq = IDSequence()

        @JvmStatic
        fun resetVisited(roots: List<SNode>) {
            for (root in roots)
                root.resetVisited()
        }

        val FN_TRUE: (SNode) -> Boolean = {true}
        val FN_NOOP: (SNode) -> Unit = {}
        val FN_NULL: (SNode) -> Nothing? = {null}
        fun <R> FN_RET(node: SNode, ret: R) = ret
    }




    /* ************ VISITOR PATTERN METHODS ************
     * There are three Visitor accepts:
     * 1. A stateless accept.
     * 2. A stateful accept that acts on the return values from children in order.
     * 3. A stateful accept that can act one at a time on values return from children.
     * Each has a guarded and an unguarded version.
     * The guarded version will not visit the same node twice (common subexpressions).
     * For #2 and #3, the guarded version memoizes the return value from the common subexpression.
    */

    /**
     * Visit each node in the DAG.
     * [preVisit] is called before visiting the node's children.
     * If [preVisit] returns false, then the children are not visited.
     * After the children are visited, [postVisit] is called.
     */
    fun accept(
            preVisit: (SNode) -> Boolean = FN_TRUE,
            postVisit: (SNode) -> Unit = FN_NOOP) {
        visitRecurse(preVisit, postVisit)
    }

    /**
     * Same as [accept], but adds a condition to [preVisit]
     * that prevents visiting the same node twice by one of two methods:
     *
     * 1. If [useInternalGuard], mark the [visited] flag of each SNode.
     * 2. Otherwise, track visited nodes in an external Set.
     *
     * @param preVisit Use [FN_TRUE] if no preVisit is needed.
     */
    inline fun acceptGuard(
            crossinline preVisit: (SNode) -> Boolean,
            noinline postVisit: (SNode) -> Unit = FN_NOOP,
            useInternalGuard: Boolean
    ) {
        val preVisitGuard: (SNode) -> Boolean
        if( useInternalGuard ) {
            resetVisited()
            preVisitGuard = {
                if (it.visited) false
                else {
                    it.visited = true
                    preVisit(it)
                }
            }
        } else {
            val seen: MutableSet<SNode> = HashSet()
            preVisitGuard = {
                if (it in seen) false
                else {
                    seen += it
                    preVisit(it)
                }
            }
        }
        accept(preVisitGuard, postVisit)
    }

    private fun visitRecurse(preVisit: (SNode) -> Boolean, postVisit: (SNode) -> Unit) {
        if (!preVisit(this))
            return
        for (i in inputs.indices)
            inputs[i].visitRecurse(preVisit, postVisit)
        postVisit(this)
    }

    /**
     * Visit each node in the DAG.
     * [preVisit] is called before visiting the node's children.
     * If [preVisit] returns a non-null, then the children are not visited and the returned value is returned.
     * After the children are visited, [postVisit] is called with the return values from the children and its result returned.
     */
    fun <R:Any> acceptFold(
            preVisit: (SNode) -> R? = FN_NULL,
            postVisit: (SNode, List<R>) -> R): R {
        return visitRecurseFold(preVisit, postVisit)
    }

    /**
     * Same as [acceptFold], but memoizes the return result of visited nodes from [postVisit]
     * via an external Map.
     * @param preVisit Use [FN_NULL] if no preVisit is needed.
     */
    inline fun <R:Any> acceptFoldGuard(
            crossinline preVisit: (SNode) -> R?,
            crossinline postVisit: (SNode, List<R>) -> R
    ): R {
        val seen: MutableMap<SNode, R?> = HashMap()
        val preVisitGuard: (SNode) -> R? = {
            if (it in seen) seen[it]
            else {
                val pre = preVisit(it)
                if (pre != null)
                    seen[it] = pre
                pre
            }
        }
        val postVisitGuard: (SNode, List<R>) -> R = { n, childRets ->
            val post = postVisit(n, childRets)
            seen[n] = post
            post
        }
        return acceptFold(preVisitGuard, postVisitGuard)
    }

    private fun <R:Any> visitRecurseFold(
            preVisit: (SNode) -> R?,
            postVisit: (SNode, List<R>) -> R
    ): R {
        val pre = preVisit(this)
        if (pre != null)
            return pre
        val childRets: MutableList<R> = ArrayList(inputs.size)
        for (i in inputs.indices)
            childRets[i] = inputs[i].visitRecurseFold(preVisit, postVisit)
        return postVisit(this, childRets)
    }


    /**
     * Visit each node in the DAG.
     * [preVisit] is called before visiting the node's children.
     * If [preVisit] returns a non-null, then the children are not visited and the returned value is returned.
     *
     * The return values from each child are folded together by [fold], starting with [default].
     * After the children are visited, [postVisit] is called with the result from the children's fold.
     */
    fun <R:Any> acceptFoldUnordered(
            preVisit: (SNode) -> R? = FN_NULL,
            postVisit: (SNode, R) -> R,
            default: R,
            fold: (R, R) -> R): R {
        return visitRecurseFoldUnordered(preVisit, postVisit, default, fold)
    }

    /**
     * Same as [acceptFoldUnordered], but memoizes the return result of visited nodes from [postVisit]
     * via an external Map.
     *
     * @param preVisit Use [FN_NULL] if no preVisit is needed.
     */
    inline fun <R:Any> acceptFoldUnorderedGuard(
            crossinline preVisit: (SNode) -> R?,
            crossinline postVisit: (SNode, R) -> R,
            default: R,
            noinline fold: (R, R) -> R
    ): R {
        val seen: MutableMap<SNode, R?> = HashMap()
        val preVisitGuard: (SNode) -> R? = {
            if (it in seen) seen[it]
            else {
                val pre = preVisit(it)
                if (pre != null)
                    seen[it] = pre
                pre
            }
        }
        val postVisitGuard: (SNode, R) -> R = { n, ret ->
            val post = postVisit(n, ret)
            seen[n] = post
            post
        }
        return acceptFoldUnordered(preVisitGuard, postVisitGuard, default, fold)
    }

    private fun <R:Any> visitRecurseFoldUnordered(
            preVisit: (SNode) -> R?,
            postVisit: (SNode, R) -> R,
            default: R,
            fold: (R, R) -> R
    ): R {
        val pre = preVisit(this)
        if (pre != null)
            return pre
        var ret = default
        for (i in inputs.indices)
            ret = fold(ret, inputs[i].visitRecurseFoldUnordered(preVisit, postVisit, default, fold))
        return postVisit(this, ret)
    }

    /** Create a copy of this SNode whose inputs point to the same inputs, adding the new copy to the inputs' parents.
     * The new copy has no parents. */
    abstract fun shallowCopyNoParentsYesInputs(): SNode

    /**
     * Compare this SNode with another based on type equality (same class, same operator, etc.)
     * and input identity equality (all inputs are referentially equal).
     */
    abstract fun compare(o: SNode): Boolean

    val ePathLabels: ArrayList<EPath> = arrayListOf()
    var cachedCost: SPCost = SPCost.ZERO_COST
    var onRootPath: Boolean = false
}

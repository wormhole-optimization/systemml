package org.apache.sysml.hops.spoof2.rewrite

import java.util.ArrayList
import org.apache.sysml.hops.spoof2.plan.SNode
import org.apache.sysml.hops.spoof2.plan.SNodeNary
import org.apache.sysml.hops.spoof2.plan.SNodeNary.NaryOp

object SNodeRewriteUtils {
    fun getChildReferencePos(parent: SNode, child: SNode): Int {
        return parent.inputs.indexOf(child)
    }

    fun removeChildReference(parent: SNode, child: SNode) {
        parent.inputs.remove(child)
        child.parents.remove(parent)
    }

    fun removeChildReferenceByPos(parent: SNode, child: SNode, posChild: Int) {
        parent.inputs.removeAt(posChild)
        child.parents.remove(parent)
    }

    fun removeAllChildReferences(parent: SNode) {
        //remove parent reference from all childs
        for (child in parent.inputs)
            child.parents.remove(parent)

        //remove all child references
        parent.inputs.clear()
    }

    fun addChildReference(parent: SNode, child: SNode) {
        parent.inputs.add(child)
        child.parents.add(parent)
    }

    fun addChildReference(parent: SNode, child: SNode, pos: Int) {
        parent.inputs.add(pos, child)
        child.parents.add(parent)
    }

    fun rewireAllParentChildReferences(hold: SNode, hnew: SNode) {
        val parents = ArrayList(hold.parents)
        for (lparent in parents)
            SNodeRewriteUtils.replaceChildReference(lparent, hold, hnew)
    }

    fun replaceChildReference(parent: SNode, inOld: SNode, inNew: SNode) {
        val pos = getChildReferencePos(parent, inOld)
        removeChildReferenceByPos(parent, inOld, pos)
        addChildReference(parent, inNew, pos)
    }

    @JvmOverloads fun replaceChildReference(parent: SNode, inOld: SNode, inNew: SNode, pos: Int, refresh: Boolean = true) {
        removeChildReferenceByPos(parent, inOld, pos)
        addChildReference(parent, inNew, pos)
    }

    fun cleanupUnreferenced(vararg inputs: SNode) {
        for (input in inputs)
            if (input.parents.isEmpty())
                removeAllChildReferences(input)
    }

    fun isSNodeNary(node: SNode, type: NaryOp): Boolean {
        return node is SNodeNary && node.op === type
    }
}

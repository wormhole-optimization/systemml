package org.apache.sysml.hops.spoof2.plan

import org.apache.sysml.api.DMLException

class SNodeException : DMLException {
    constructor(message: String): super(message)
    constructor(cause: Throwable) : super(cause)
    constructor(message: String, cause: Throwable) : super(message, cause)
    constructor(sop: SNode, message: String): super("$sop id=${sop.id} ${sop.schema}: $message")
    constructor(sop: SNode, message: String, cause: Throwable) : super("$sop id=${sop.id} ${sop.schema}: $message", cause)

    companion object {
        private const val serialVersionUID = 1L

        /**
         * If the condition fails, print the Op and its Id, along with the message formatted with objects.
         * @param condition Condition to test
         * @param message Message to print if the condition fails
         * @throws SNodeException Thrown if condition is false
         */
        @Throws(SNodeException::class)
        inline fun check(condition: Boolean, sop: SNode, message: () -> String) {
            if (!condition)
                throw SNodeException(sop, message())
        }
    }
}
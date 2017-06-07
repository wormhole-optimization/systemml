package org.apache.sysml.hops.spoof2.rewrite;

import org.apache.commons.logging.Log;
import org.apache.commons.logging.LogFactory;
import org.apache.sysml.hops.spoof2.plan.SNode;

public abstract class SPlanRewriteRule 
{
	protected static final Log LOG = LogFactory.getLog(SPlanRewriteRule.class.getName());
	
	public abstract SNode rewriteNode(SNode parent, SNode node, int pos);
}

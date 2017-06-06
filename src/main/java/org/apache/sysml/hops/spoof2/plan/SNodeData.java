package org.apache.sysml.hops.spoof2.plan;

import org.apache.sysml.hops.Hop;
import org.apache.sysml.hops.LiteralOp;

public class SNodeData extends SNode
{
	private final Hop _hopRef;
	
	public SNodeData(Hop hop) {
		super();
		_hopRef = hop;
		setupBasicSchema(_hopRef.getHopID());
	}
	
	public SNodeData(SNode input, Hop hop) {
		super(input);
		_hopRef = hop;
		setupBasicSchema(_hopRef.getHopID());
	}
	
	public Hop getHop() {
		return _hopRef;
	}
	
	public boolean isLiteral() {
		return (_hopRef instanceof LiteralOp);
	}

	@Override
	public boolean isIndexAggregator() {
		return false;
	}

	@Override
	public boolean isIndexPropagator() {
		return false;
	}

	@Override
	public String toString() {
		return "data("+_hopRef.getHopID()
			+" "+_hopRef.getOpString()+")";
	}
}

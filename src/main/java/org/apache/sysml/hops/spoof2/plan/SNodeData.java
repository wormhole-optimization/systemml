package org.apache.sysml.hops.spoof2.plan;

import org.apache.sysml.hops.Hop;

public class SNodeData extends SNode
{
	private final Hop _hopRef;
	
	public SNodeData(Hop hop) {
		_hopRef = hop;
		_schema = hop.getDataType().isMatrix() ?
			new Indexes("i1_"+hop.getHopID(), "i2_"+hop.getHopID()) :
			new Indexes();
	}
	
	public SNodeData(Hop hop, SNode input) {
		super(input);
		_hopRef = hop;
	}
	
	public Hop getHop() {
		return _hopRef;
	}
}

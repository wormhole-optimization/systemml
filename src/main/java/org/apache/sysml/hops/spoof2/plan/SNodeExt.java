package org.apache.sysml.hops.spoof2.plan;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.apache.sysml.hops.Hop;

public class SNodeExt extends SNode
{
	private final Hop _hopRef;
	
	public SNodeExt(Hop hop) {
		this(new ArrayList<SNode>(), hop);
	}
	
	public SNodeExt(SNode input, Hop hop) {
		this(Arrays.asList(input), hop);
	}
	
	public SNodeExt(List<SNode> inputs, Hop hop) {
		super(inputs);
		_hopRef = hop;
		setupBasicSchema(_hopRef.getHopID());		
	}
	
	public Hop getHop() {
		return _hopRef;
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
		return "ext("+_hopRef.getHopID()
			+" "+_hopRef.getOpString()+")";
	}
}

package org.apache.sysml.hops.spoof2.plan;


import org.apache.sysml.hops.Hop.AggOp;

public class SNodeAggregate extends SNode
{
	//reuse of hop aggregation types
	private final AggOp _type;

	public SNodeAggregate(SNode inputs, AggOp type) {
		super(inputs);
		_type = type;
	}
	
	public AggOp getOp() {
		return _type;
	}
}

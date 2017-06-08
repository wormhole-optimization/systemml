package org.apache.sysml.hops.spoof2.plan;


import java.util.List;

import org.apache.sysml.hops.Hop.AggOp;

public class SNodeAggregate extends SNode
{
	//reuse of hop aggregation types
	private final AggOp _type;

	public SNodeAggregate(SNode input, AggOp type) {
		super(input);
		_type = type;
	}
	
	public SNodeAggregate(SNode input, AggOp type, List<String> schema) {
		super(input);
		_type = type;
		_schema.addAll(schema);
	}
	
	public AggOp getOp() {
		return _type;
	}

	@Override
	public boolean isIndexAggregator() {
		return false;
	}

	@Override
	public boolean isIndexPropagator() {
		return true;
	}

	@Override
	public String toString() {
		return "agg("+_type.name().toLowerCase()+")";
	}
}
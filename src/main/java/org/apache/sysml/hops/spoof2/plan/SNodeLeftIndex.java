package org.apache.sysml.hops.spoof2.plan;

public class SNodeLeftIndex extends SNode
{

	@Override
	public boolean isIndexAggregator() {
		return true;
	}

	@Override
	public boolean isIndexPropagator() {
		return false;
	}

	@Override
	public String toString() {
		// TODO Auto-generated method stub
		return null;
	}

}

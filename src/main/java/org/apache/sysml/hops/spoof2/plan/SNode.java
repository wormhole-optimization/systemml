package org.apache.sysml.hops.spoof2.plan;

import java.util.ArrayList;
import java.util.List;

import org.apache.sysml.runtime.controlprogram.parfor.util.IDSequence;

public abstract class SNode 
{
	private final static IDSequence _idSeq = new IDSequence();
	
	//globally unique SNode id
	private final long _ID;
	//SNode parent nodes
	private final ArrayList<SNode> _parents;
	//SNode child nodes and associated indexes
	private final ArrayList<SNode> _inputs;
	private final ArrayList<Indexes> _indexes;
	
	//output dimensions and meta data
	protected final ArrayList<String> _schema;
	protected long[] _dims;
	
	public SNode() {
		_ID = _idSeq.getNextID();
		_parents = new ArrayList<SNode>();
		_inputs = new ArrayList<SNode>();
		_indexes = new ArrayList<Indexes>();
		_schema = new ArrayList<String>();
	}

	public SNode(SNode input) {
		this();
		_inputs.add(input);
		input._parents.add(this);
	}
	
	public SNode(List<SNode> inputs) {
		this();
		for( SNode input : inputs ) {
			_inputs.add(input);
			input._parents.add(this);
		}
	}

	public long getID() {
		return _ID;
	}
	
	public List<SNode> getParent() {
		return _parents;
	}
	
	public List<SNode> getInput() {
		return _inputs;
	}
	
	public List<Indexes> getIndexes() {
		return _indexes;
	}
	
	public List<String> getSchema() {
		return _schema;
	}
	
	public int getNumDims() {
		return _dims.length;
	}
	
	public long getDim(int pos) {
		return _dims[pos];
	}
	
	public long getDim1() {
		return getDim(0);
	}
	
	public long getDim2() {
		return (getNumDims() >= 2) ?
			getDim(1) : 1;
	}
	
	public void setDims(Long... dims) {
		_dims = new long[dims.length];
		for( int i=0; i<dims.length; i++ )
			_dims[i] = dims[i]; //unboxing
	}
	
	public abstract boolean isIndexAggregator();
	
	public abstract boolean isIndexPropagator();
	
	@Override
	public abstract String toString();
	
	protected void setupBasicSchema(long hopID) {
		_schema.add("i1_" + hopID);
		_schema.add("i2_" + hopID);
	}
}

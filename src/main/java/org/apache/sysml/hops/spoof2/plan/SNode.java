package org.apache.sysml.hops.spoof2.plan;

import java.util.ArrayList;

import org.apache.sysml.runtime.controlprogram.parfor.util.IDSequence;

public class SNode 
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
	protected Indexes _schema;
	protected long[] _dims;
	
	public SNode() {
		_ID = _idSeq.getNextID();
		_parents = new ArrayList<SNode>();
		_inputs = new ArrayList<SNode>();
		_indexes = new ArrayList<Indexes>();
	}

	public SNode(SNode input) {
		this();
		_inputs.add(input);
		input._parents.add(this);
	}
	
	public SNode(ArrayList<SNode> inputs) {
		this();
		for( SNode input : inputs ) {
			_inputs.add(input);
			input._parents.add(this);
		}
	}

	public long getID() {
		return _ID;
	}
	
	public ArrayList<SNode> getParent() {
		return _parents;
	}
	
	public ArrayList<SNode> getInput() {
		return _inputs;
	}
	
	public ArrayList<Indexes> getIndexes() {
		return _indexes;
	}
	
	public Indexes getSchema() {
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
}

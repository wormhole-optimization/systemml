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
	protected boolean _visited;
	
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
	
	public void setSchema(List<String> schema) {
		_schema.clear();
		_schema.addAll(schema);
	}
	
	public boolean isScalar() {
		return (_dims.length==0)
			|| (_dims.length==2 && _dims[0]==0 && _dims[1]==0);
	}
	
	public int getNumDims() {
		return _dims.length;
	}
	
	public long getDim(int pos) {
		return _dims[pos];
	}
	
	public long getDim(String attr) {
		return _dims[_schema.indexOf(attr)];
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
	
	public boolean isVisited() {
		return _visited;
	}
	
	public void setVisited() {
		setVisited(true);
	}
	
	public void setVisited(boolean flag) {
		_visited = flag;
	}
	
	public void resetVisited() {
		if( !isVisited() )
			return;
		for( SNode c : getInput() )
			c.resetVisited();		
		setVisited(false);
	}
	
	public static void resetVisited(ArrayList<SNode> roots) {
		for( SNode root : roots )
			root.resetVisited();
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
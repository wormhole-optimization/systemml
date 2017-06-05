package org.apache.sysml.hops.spoof2.plan;

import java.util.ArrayList;
import java.util.Arrays;

import org.apache.sysml.runtime.controlprogram.parfor.util.IDSequence;

public class Indexes 
{
	private final static IDSequence _idSeq = new IDSequence();
	
	private final ArrayList<String> _names;

	public Indexes(Indexes indexes) {
		_names = new ArrayList<String>(
			indexes._names);
	}
	
	public Indexes(String... indexes) {
		_names = new ArrayList<String>();
		for( String index : indexes )
			_names.add(index);
	}
	
	public void add(String index) {
		_names.add(index);
	}
	
	public String get(int pos) {
		return _names.get(pos);
	}
	
	public void rename(String oldindex, String index) {
		_names.remove(oldindex);
		_names.add(index);
	}
	
	public boolean contains(String index) {
		return _names.contains(index);
	}
	
	public int size() {
		return _names.size();
	}
	
	@Override
	public String toString() {
		return "(IX: "+Arrays.toString(
			_names.toArray(new String[0]))+")";
	}
	
	public static String getNextIndex() {
		return "i" + _idSeq.getNextID();
	}
}

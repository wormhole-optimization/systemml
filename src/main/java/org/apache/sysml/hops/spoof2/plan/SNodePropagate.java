package org.apache.sysml.hops.spoof2.plan;

import java.util.ArrayList;

import org.apache.commons.lang.ArrayUtils;

public class SNodePropagate extends SNode
{
	public enum PropOp {
		//unary operators
		
		//binary operators
		PLUS, MINUS, MULT, DIV, MODULUS, INTDIV, 
		LESS, LESSEQUAL, GREATER, GREATEREQUAL, EQUAL, NOTEQUAL, 
		MIN, MAX, AND, OR, LOG, POW, 
		
		//ternary operators
	};
	
	private final PropOp _type;

	public SNodePropagate(SNode input, PropOp type) {
		super(input);
		_type = type;
		
		//for unary ops, schema propagates
		_schema = new Indexes(input.getSchema());
	}
	
	//TODO better formulation of join indexes
	public SNodePropagate(ArrayList<SNode> inputs, PropOp type, Integer... joinDims) {
		super(inputs);
		_type = type;
		
		//for n-ary ops, the schema is the union which contains 
		//the join indexes just once
		_schema = new Indexes(inputs.get(0).getSchema());
		for( int i=0; i<inputs.size(); i++ ) {
			Indexes schemaI = inputs.get(i).getSchema();
			for( int j=0; j<schemaI.size(); j++ )
				if( !ArrayUtils.contains(joinDims, j) )
					_schema.add(schemaI.get(j));
		}
	}
	
	public PropOp getOp() {
		return _type;
	}
}

package org.apache.sysml.hops.spoof2.plan;

import java.util.ArrayList;

public class SNodeNary extends SNode
{
	public enum NaryOp {
		//unary operations
		NOT, ABS, SIN, COS, TAN, ASIN, ACOS, ATAN, SIGN, SQRT, LOG, EXP, 
		ROUND, CEIL, FLOOR, 
		SPROP, SIGMOID, SELP, LOG_NZ, 
		
		//binary operations
		PLUS, MINUS, MULT, DIV, MODULUS, INTDIV, 
		LESS, LESSEQUAL, GREATER, GREATEREQUAL, EQUAL, NOTEQUAL, 
		MIN, MAX, AND, OR, POW, //LOG (see unary)
		
		//ternary operations
		PLUS_MULT, MINUS_MULT,
		
		//reorg operations
		TRANSPOSE;
		
		public static boolean contains(String value) {
			for( NaryOp nt : values()  )
				if( nt.name().equals(value) )
					return true;
			return false;
		}
	};
	
	private final NaryOp _type;
	private final JoinCondition[] _joins;
	
	public SNodeNary(SNode input, NaryOp type) {
		super(input);
		_type = type;
		
		//for unary ops, schema propagates
		_joins = new JoinCondition[0];
		_schema.addAll(input.getSchema());
	}
	
	public SNodeNary(ArrayList<SNode> inputs, NaryOp type, JoinCondition... joins) {
		super(inputs);
		_type = type;
		
		//for n-ary ops, the schema is the union which contains 
		//the join indexes just once
		_joins = joins;
		for(SNode input : inputs)
			_schema.addAll(input.getSchema());
		for(JoinCondition cond : joins)
			_schema.remove(cond.getRight());
	}
	
	public NaryOp getOp() {
		return _type;
	}
	
	public JoinCondition[] getJoins() {
		return _joins;
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
		return "nary("+_type.name()+")";
	}

	//equi join condition, use multiple for conjunctions
	public static class JoinCondition {
		private final String _leftIndex;
		private final String _rightIndex;
		
		public JoinCondition(String left, String right) {
			_leftIndex = left;
			_rightIndex = right;
		}
		
		public String getLeft() {
			return _leftIndex;
		}
		
		public String getRight() {
			return _rightIndex;
		}
	}
}

package org.apache.sysml.hops.spoof2;

import java.util.ArrayList;
import java.util.Arrays;

import org.apache.commons.logging.Log;
import org.apache.commons.logging.LogFactory;
import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.apache.sysml.hops.AggBinaryOp;
import org.apache.sysml.hops.AggUnaryOp;
import org.apache.sysml.hops.DataOp;
import org.apache.sysml.hops.Hop;
import org.apache.sysml.hops.Hop.AggOp;
import org.apache.sysml.hops.HopsException;
import org.apache.sysml.hops.LiteralOp;
import org.apache.sysml.hops.spoof2.plan.SNode;
import org.apache.sysml.hops.spoof2.plan.SNodeAggregate;
import org.apache.sysml.hops.spoof2.plan.SNodeData;
import org.apache.sysml.hops.spoof2.plan.SNodePropagate;
import org.apache.sysml.hops.spoof2.plan.SNodePropagate.PropOp;
import org.apache.sysml.parser.DMLProgram;
import org.apache.sysml.parser.ForStatement;
import org.apache.sysml.parser.ForStatementBlock;
import org.apache.sysml.parser.FunctionStatement;
import org.apache.sysml.parser.FunctionStatementBlock;
import org.apache.sysml.parser.IfStatement;
import org.apache.sysml.parser.IfStatementBlock;
import org.apache.sysml.parser.LanguageException;
import org.apache.sysml.parser.StatementBlock;
import org.apache.sysml.parser.WhileStatement;
import org.apache.sysml.parser.WhileStatementBlock;
import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.utils.Explain;

public class Spoof2Compiler 
{
	private static final Log LOG = LogFactory.getLog(Spoof2Compiler.class.getName());
	
	//internal configuration flags
	public static boolean LDEBUG = true;
	
	static {
		// for internal debugging only
		if( LDEBUG ) {
			Logger.getLogger("org.apache.sysml.hops.spoof2")
				  .setLevel((Level) Level.TRACE);
		}
	}
	
	
	public static void generateCode(DMLProgram dmlprog) 
		throws LanguageException, HopsException, DMLRuntimeException
	{
		// for each namespace, handle function statement blocks
		for (String namespaceKey : dmlprog.getNamespaces().keySet()) {
			for (String fname : dmlprog.getFunctionStatementBlocks(namespaceKey).keySet()) {
				FunctionStatementBlock fsblock = dmlprog.getFunctionStatementBlock(namespaceKey,fname);
				generateCodeFromStatementBlock(fsblock);
			}
		}
		
		// handle regular statement blocks in "main" method
		for (int i = 0; i < dmlprog.getNumStatementBlocks(); i++) {
			StatementBlock current = dmlprog.getStatementBlock(i);
			generateCodeFromStatementBlock(current);
		}
	}
	
	public static void generateCodeFromStatementBlock(StatementBlock current)
		throws HopsException, DMLRuntimeException
	{
		if (current instanceof FunctionStatementBlock)
		{
			FunctionStatementBlock fsb = (FunctionStatementBlock)current;
			FunctionStatement fstmt = (FunctionStatement)fsb.getStatement(0);
			for (StatementBlock sb : fstmt.getBody())
				generateCodeFromStatementBlock(sb);
		}
		else if (current instanceof WhileStatementBlock)
		{
			WhileStatementBlock wsb = (WhileStatementBlock) current;
			WhileStatement wstmt = (WhileStatement)wsb.getStatement(0);
			wsb.setPredicateHops(optimize(wsb.getPredicateHops(), false));
			for (StatementBlock sb : wstmt.getBody())
				generateCodeFromStatementBlock(sb);
		}
		else if (current instanceof IfStatementBlock)
		{
			IfStatementBlock isb = (IfStatementBlock) current;
			IfStatement istmt = (IfStatement)isb.getStatement(0);
			isb.setPredicateHops(optimize(isb.getPredicateHops(), false));
			for (StatementBlock sb : istmt.getIfBody())
				generateCodeFromStatementBlock(sb);
			for (StatementBlock sb : istmt.getElseBody())
				generateCodeFromStatementBlock(sb);
		}
		else if (current instanceof ForStatementBlock) //incl parfor
		{
			ForStatementBlock fsb = (ForStatementBlock) current;
			ForStatement fstmt = (ForStatement)fsb.getStatement(0);
			fsb.setFromHops(optimize(fsb.getFromHops(), false));
			fsb.setToHops(optimize(fsb.getToHops(), false));
			fsb.setIncrementHops(optimize(fsb.getIncrementHops(), false));
			for (StatementBlock sb : fstmt.getBody())
				generateCodeFromStatementBlock(sb);
		}
		else //generic (last-level)
		{
			current.set_hops( generateCodeFromHopDAGs(current.get_hops()) );
			current.updateRecompilationFlag();
		}
	}

	public static ArrayList<Hop> generateCodeFromHopDAGs(ArrayList<Hop> roots) 
		throws HopsException, DMLRuntimeException
	{
		if( roots == null )
			return roots;

		ArrayList<Hop> optimized = optimize(roots, false);
		Hop.resetVisitStatus(roots);
		Hop.resetVisitStatus(optimized);
		
		return optimized;
	}
	
	
	/**
	 * Main interface of sum-product optimizer, predicate dag.
	 * 
	 * @param root dag root node
	 * @param recompile true if invoked during dynamic recompilation
	 * @return dag root node of modified dag
	 * @throws DMLRuntimeException if optimization failed
	 */
	public static Hop optimize( Hop root, boolean recompile ) throws DMLRuntimeException {
		if( root == null )
			return root;
		
		return optimize(new ArrayList<Hop>(Arrays.asList(root)), recompile).get(0);
	}
	
	/**
	 * Main interface of sum-product optimizer, statement block dag.
	 * 
	 * @param roots dag root nodes
	 * @param recompile true if invoked during dynamic recompilation
	 * @return dag root nodes of modified dag 
	 * @throws DMLRuntimeException if optimization failed
	 */
	public static ArrayList<Hop> optimize(ArrayList<Hop> roots, boolean recompile) 
		throws DMLRuntimeException 
	{
		LOG.trace("Spoof2Compiler called for HOP DAG: \n" 
			+ Explain.explainHops(roots));
		
		//construct sum-product plan
		ArrayList<SNode> sroots = new ArrayList<SNode>();
		for( Hop root : roots )
			sroots.add(rConstructSumProductPlan(root));
		
		//TODO explain extension sum-product plan
		
		//rewrite sum-product plan
		
		
		//re-construct modified HOP DAG
		
		
		return roots;
	}
	
	private static SNode rConstructSumProductPlan(Hop current) {
		//recursively process child nodes
		ArrayList<SNode> inputs = new ArrayList<SNode>();
		for( Hop c : current.getInput() )
			inputs.add(rConstructSumProductPlan(c));
		
		//construct node for current hop
		SNode node = null;
		
		
		if( current instanceof DataOp ) {
			node = ((DataOp)current).isRead() ?
				new SNodeData(current) : 
				new SNodeData(current, inputs.get(0));
			node.setDims(current.getDim1(), current.getDim2());
		}
		else if( current instanceof LiteralOp ) {
			node = new SNodeData(current);
		}
		else if( current instanceof AggUnaryOp ) {
			node = new SNodeAggregate(inputs.get(0), 
				((AggUnaryOp)current).getOp());
		}
		else if( current instanceof AggBinaryOp ) {
			SNode mult = new SNodePropagate(inputs, PropOp.MULT);
			node = new SNodeAggregate(mult, AggOp.SUM);
		}
		
		return node;
	}
}

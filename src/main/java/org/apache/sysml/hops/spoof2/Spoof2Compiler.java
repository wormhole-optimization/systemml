package org.apache.sysml.hops.spoof2;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.apache.commons.logging.Log;
import org.apache.commons.logging.LogFactory;
import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.apache.sysml.hops.AggBinaryOp;
import org.apache.sysml.hops.AggUnaryOp;
import org.apache.sysml.hops.BinaryOp;
import org.apache.sysml.hops.DataGenOp;
import org.apache.sysml.hops.DataOp;
import org.apache.sysml.hops.Hop;
import org.apache.sysml.hops.Hop.AggOp;
import org.apache.sysml.hops.Hop.Direction;
import org.apache.sysml.hops.Hop.OpOp1;
import org.apache.sysml.hops.Hop.OpOp2;
import org.apache.sysml.hops.Hop.OpOp3;
import org.apache.sysml.hops.HopsException;
import org.apache.sysml.hops.LiteralOp;
import org.apache.sysml.hops.ReorgOp;
import org.apache.sysml.hops.UnaryOp;
import org.apache.sysml.hops.rewrite.HopRewriteUtils;
import org.apache.sysml.hops.rewrite.ProgramRewriteStatus;
import org.apache.sysml.hops.rewrite.ProgramRewriter;
import org.apache.sysml.hops.spoof2.plan.SNode;
import org.apache.sysml.hops.spoof2.plan.SNodeAggregate;
import org.apache.sysml.hops.spoof2.plan.SNodeData;
import org.apache.sysml.hops.spoof2.plan.SNodeExt;
import org.apache.sysml.hops.spoof2.plan.SNodeNary;
import org.apache.sysml.hops.spoof2.plan.SNodeNary.JoinCondition;
import org.apache.sysml.hops.spoof2.plan.SNodeNary.NaryOp;
import org.apache.sysml.hops.spoof2.rewrite.BasicSPlanRewriter;
import org.apache.sysml.hops.spoof2.rewrite.SNodeRewriteUtils;
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
import org.spark_project.guava.collect.Lists;

public class Spoof2Compiler 
{
	private static final Log LOG = LogFactory.getLog(Spoof2Compiler.class.getName());
	
	//internal configuration flags
	public static boolean LDEBUG = true;
	
	static {
		// for internal debugging only
		if( LDEBUG ) {
			Logger.getLogger("org.apache.sysml.hops.spoof2")
				  .setLevel(Level.TRACE);
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
			return null;

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
	 * @throws HopsException -
	 */
	public static Hop optimize( Hop root, boolean recompile ) throws DMLRuntimeException, HopsException {
		if( root == null )
			return null;
		return optimize(new ArrayList<Hop>(Arrays.asList(root)), recompile).get(0);
	}
	
	/**
	 * Main interface of sum-product optimizer, statement block dag.
	 * 
	 * @param roots dag root nodes
	 * @param recompile true if invoked during dynamic recompilation
	 * @return dag root nodes of modified dag 
	 * @throws DMLRuntimeException if optimization failed
	 * @throws HopsException -
	 */
	public static ArrayList<Hop> optimize(ArrayList<Hop> roots, boolean recompile) 
		throws DMLRuntimeException, HopsException 
	{
		if( LOG.isTraceEnabled() ) {
			LOG.trace("Spoof2Compiler called for HOP DAG: \n" 
				+ Explain.explainHops(roots));
		}
		
		//construct sum-product plan
		ArrayList<SNode> sroots = new ArrayList<>();
		for( Hop root : roots )
			sroots.add(rConstructSumProductPlan(root));
		
		if( LOG.isTraceEnabled() ) {
			LOG.trace("Explain after initial SPlan construction: " 
				+ Explain.explainSPlan(sroots));
		}
		
		//rewrite sum-product plan
		BasicSPlanRewriter rewriter = new BasicSPlanRewriter();
		sroots = rewriter.rewriteSPlan(sroots);
		
		if( LOG.isTraceEnabled() ) {
			LOG.trace("Explain after SPlan rewriting: " 
				+ Explain.explainSPlan(sroots));
		}
		
		//re-construct modified HOP DAG
		ArrayList<Hop> roots2 = new ArrayList<>();
		for( SNode sroot : sroots )
			roots2.add(rReconstructHopDag(sroot));
		
		if( LOG.isTraceEnabled() ) {
			LOG.trace("Spoof2Compiler created modified HOP DAG: \n" 
				+ Explain.explainHops(roots2));
		}
		
		//rewrite after applied sum-product optimizer
		Hop.resetVisitStatus(roots2);
		ProgramRewriter rewriter2 = new ProgramRewriter(true, true);
		roots2 = rewriter2.rewriteHopDAGs(roots2, new ProgramRewriteStatus());
	
		if( LOG.isTraceEnabled() ) {
			LOG.trace("Spoof2Compiler rewritten modified HOP DAG: \n" 
				+ Explain.explainHops(roots2));
		}
		
		return roots2;
	}
	
	private static SNode rConstructSumProductPlan(Hop current) {
		//recursively process child nodes
		ArrayList<SNode> inputs = new ArrayList<>();
		for( Hop c : current.getInput() )
			inputs.add(rConstructSumProductPlan(c));
		
		//construct node for current hop
		SNode node = null;
		if( current instanceof DataOp ) {
			node = ((DataOp)current).isWrite() ?
				new SNodeData(inputs.get(0), current) : 
				new SNodeData(current);
		}
		else if( current instanceof LiteralOp ) {
			node = new SNodeData(current);
		}
		else if( current instanceof DataGenOp ) {
			node = new SNodeExt(current);
		}
		else if( current instanceof ReorgOp ) {
			node = HopRewriteUtils.isTransposeOperation(current) ?
				new SNodeNary(inputs.get(0), NaryOp.TRANSPOSE,
					Lists.reverse(inputs.get(0).getSchema())):
				new SNodeExt(inputs.get(0), current);
		}
		else if( current instanceof UnaryOp ) {
			OpOp1 op = ((UnaryOp) current).getOp();
			node = NaryOp.contains(op.name()) ?
				new SNodeNary(inputs.get(0), NaryOp.valueOf(op.name())) :
				new SNodeExt(inputs.get(0), current);
		}
		else if( current instanceof BinaryOp ) {
			OpOp2 op = ((BinaryOp) current).getOp();
			node = NaryOp.contains(op.name()) ?
				new SNodeNary(inputs, NaryOp.valueOf(op.name())) :
				new SNodeExt(inputs, current);			
		}
		else if( current instanceof AggUnaryOp ) {
			AggUnaryOp au = (AggUnaryOp) current;
			List<String> schema = (au.getDirection()==Direction.Row) ? 
				Arrays.asList(inputs.get(0).getSchema().get(0)) : (au.getDirection()==Direction.Col) ? 
				Arrays.asList(inputs.get(0).getSchema().get(1)) : new ArrayList<String>();
			node = new SNodeAggregate(inputs.get(0), 
				((AggUnaryOp)current).getOp(), schema);
		}
		else if( current instanceof AggBinaryOp ) {
			SNode mult = new SNodeNary(inputs, NaryOp.MULT, 
				new JoinCondition(inputs.get(0).getSchema().get(1),
				inputs.get(1).getSchema().get(0)));
			mult.setDims(current.getDim1(), current.getDim2(), 
				current.getInput().get(0).getDim2());
			node = new SNodeAggregate(mult, AggOp.SUM, Arrays.asList(
				mult.getSchema().get(0), mult.getSchema().get(2)));
		}
		
		//check for valid created SNode
		if( node == null ) {
			throw new RuntimeException("Error constructing SNode for HOP: " +
				current.getHopID() + " " + current.getOpString() + ".");
		}
		
		//update size information (other than intermediates)
		node.setDims(current.getDim1(), current.getDim2());
		
		return node;
	}
	
	private static Hop rReconstructHopDag(SNode current) {
		
		//recursively process child nodes
		ArrayList<Hop> inputs = new ArrayList<Hop>();
		for( SNode c : current.getInput() )
			inputs.add(rReconstructHopDag(c));
		
		Hop node = null;
		
		if( current instanceof SNodeData ) {
			node = ((SNodeData)current).getHop();
			if( !current.getInput().isEmpty() ) {
				HopRewriteUtils.replaceChildReference(node, 
					node.getInput().get(0), inputs.get(0), 0);
			}
		}
		else if( current instanceof SNodeAggregate ) {
			SNodeAggregate agg = (SNodeAggregate) current;
			if( SNodeRewriteUtils.isSNodeNary(agg.getInput().get(0), NaryOp.MULT) 
				&& (agg.isScalar() || agg.getInput().get(0).getNumDims()==3) ) {
				//TODO proper handling of schemas to decide upon transpose
				Hop input1 = inputs.get(0).getInput().get(0);
				Hop input2 = inputs.get(0).getInput().get(1);
				input1 = (agg.isScalar() && input1.getDim1() > 1) ? 
					HopRewriteUtils.createTranspose(input1) : input1;
				input2 = (agg.isScalar() && input2.getDim2() > 1) ? 
						HopRewriteUtils.createTranspose(input2) : input2;
				node = HopRewriteUtils.createMatrixMultiply(input1, input2);
				node = HopRewriteUtils.createUnary(node, OpOp1.CAST_AS_SCALAR);
			}
			else {
				Direction dir = agg.getSchema().isEmpty() ? Direction.RowCol : 
					agg.getSchema().get(0).equals(agg.getInput().get(0).getSchema().get(0)) ? 
					Direction.Row : Direction.Col;
				node = HopRewriteUtils.createAggUnaryOp(inputs.get(0), agg.getOp(), dir);
			}
		}
		else if( current instanceof SNodeNary ) {
			SNodeNary nary = (SNodeNary) current;
			if( inputs.size()==1 ) { //unary
				if( nary.getOp()==NaryOp.TRANSPOSE )
					node = HopRewriteUtils.createTranspose(inputs.get(0));
				else
					node = HopRewriteUtils.createUnary(
						inputs.get(0), OpOp1.valueOf(nary.getOp().name()));
			}
			else if( inputs.size()==2 ) { //binary
				node = HopRewriteUtils.createBinary(inputs.get(0), 
					inputs.get(1), OpOp2.valueOf(nary.getOp().name()));
			}
			else if( inputs.size()==3 ) { //ternary
				node = HopRewriteUtils.createTernary(inputs.get(0), inputs.get(1), 
					inputs.get(2), OpOp3.valueOf(nary.getOp().name()));
			}
		}
		else if( current instanceof SNodeExt ) {
			node = ((SNodeExt)current).getHop();
			if( !inputs.isEmpty() ) { //robustness datagen
				HopRewriteUtils.removeAllChildReferences(node);
				for( Hop c : inputs )
					node.addInput(c);
			}
		}
		
		//check for valid created SNode
		if( node == null ) {
			throw new RuntimeException("Error constructing Hop for SNode: " +
				current.getId() + " " + current.toString() + ".");
		}
		
		return node;
	} 
}

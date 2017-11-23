/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 * 
 *   http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */

package org.apache.sysml.hops;

import org.apache.sysml.api.DMLScript;
import org.apache.sysml.hops.AggBinaryOp.SparkAggType;
import org.apache.sysml.hops.rewrite.HopRewriteUtils;
import org.apache.sysml.lops.Aggregate;
import org.apache.sysml.lops.Data;
import org.apache.sysml.lops.Group;
import org.apache.sysml.lops.Lop;
import org.apache.sysml.lops.LopsException;
import org.apache.sysml.lops.RightIndex;
import org.apache.sysml.lops.LopProperties.ExecType;
import org.apache.sysml.parser.Expression.DataType;
import org.apache.sysml.parser.Expression.ValueType;
import org.apache.sysml.runtime.matrix.MatrixCharacteristics;

//for now only works for range based indexing op
public class IndexingOp extends Hop 
{
	public static String OPSTRING = "rix"; //"Indexing";
	
	private boolean _rowLowerEqualsUpper = false;
	private boolean _colLowerEqualsUpper = false;
	
	private enum IndexingMethod { 
		CP_RIX, //in-memory range index
		MR_RIX, //general case range reindex
		MR_VRIX, //vector (row/col) range index
	}
	
	
	private IndexingOp() {
		//default constructor for clone
	}
	
	//right indexing doesn't really need the dimensionality of the left matrix
	//private static Lops dummy=new Data(null, Data.OperationTypes.READ, null, "-1", DataType.SCALAR, ValueType.INT, false);
	public IndexingOp(String l, DataType dt, ValueType vt, Hop inpMatrix, Hop inpRowL, Hop inpRowU, Hop inpColL, Hop inpColU, boolean passedRowsLEU, boolean passedColsLEU) {
		super(l, dt, vt);

		getInput().add(0, inpMatrix);
		getInput().add(1, inpRowL);
		getInput().add(2, inpRowU);
		getInput().add(3, inpColL);
		getInput().add(4, inpColU);
		
		// create hops if one of them is null
		inpMatrix.getParent().add(this);
		inpRowL.getParent().add(this);
		inpRowU.getParent().add(this);
		inpColL.getParent().add(this);
		inpColU.getParent().add(this);
		
		// set information whether left indexing operation involves row (n x 1) or column (1 x m) matrix
		setRowLowerEqualsUpper(passedRowsLEU);
		setColLowerEqualsUpper(passedColsLEU);
	}

	@Override
	public void checkArity() throws HopsException {
		HopsException.check(_input.size() == 5, this, "should have 5 inputs but has %d inputs", _input.size());
	}

	public boolean isRowLowerEqualsUpper(){
		return _rowLowerEqualsUpper;
	}
	
	public boolean isColLowerEqualsUpper() {
		return _colLowerEqualsUpper;
	}
	
	public void setRowLowerEqualsUpper(boolean passed){
		_rowLowerEqualsUpper  = passed;
	}
	
	public void setColLowerEqualsUpper(boolean passed) {
		_colLowerEqualsUpper = passed;
	}
	
	@Override
	public boolean isGPUEnabled() {
		if(!DMLScript.USE_ACCELERATOR) {
			return false;
		}
		else {
			// Indexing is only supported on GPU if:
			// 1. the input is of type matrix AND
			// 2. the input is less than 2GB. 
			// The second condition is added for following reason:
			// 1. Indexing is a purely memory-bound operation and doesnot benefit drastically from pushing down to GPU.
			// 2. By forcing larger matrices to GPU (for example: training dataset), we run into risk of unnecessary evictions of 
			// parameters and the gradients. For single precision, there is additional overhead of converting training dataset 
			// to single precision every single time it is evicted.
			return (getDataType() == DataType.MATRIX) && getInputMemEstimate() < 2e+9;
		}
	}

	@Override
	public Lop constructLops()
		throws HopsException, LopsException 
	{	
		//return already created lops
		if( getLops() != null )
			return getLops();

		Hop input = getInput().get(0);
		
		//rewrite remove unnecessary right indexing
		if( HopRewriteUtils.isUnnecessaryRightIndexing(this) ) {
			setLops( input.constructLops() );
		}
		//actual lop construction, incl operator selection 
		else
		{
			try {
				ExecType et = optFindExecType();
				if(et == ExecType.MR) {
					IndexingMethod method = optFindIndexingMethod( _rowLowerEqualsUpper, _colLowerEqualsUpper,
							                                       input._dim1, input._dim2, _dim1, _dim2);
					
					Lop dummy = Data.createLiteralLop(ValueType.INT, Integer.toString(-1));
					RightIndex reindex = new RightIndex(
							input.constructLops(), getInput().get(1).constructLops(), getInput().get(2).constructLops(),
							getInput().get(3).constructLops(), getInput().get(4).constructLops(), dummy, dummy,
							getDataType(), getValueType(), et);
	
					setOutputDimensions(reindex);
					setLineNumbers(reindex);
					
					if( method == IndexingMethod.MR_RIX )
					{
						Group group1 = new Group( reindex, Group.OperationTypes.Sort, 
								DataType.MATRIX, getValueType());
						setOutputDimensions(group1);
						setLineNumbers(group1);
		
						Aggregate agg1 = new Aggregate(
								group1, Aggregate.OperationTypes.Sum, DataType.MATRIX,
								getValueType(), et);
						setOutputDimensions(agg1);
						setLineNumbers(agg1);
						
						setLops(agg1);
					}
					else //method == IndexingMethod.MR_VRIX
					{
						setLops(reindex);
					}
				}
				else if( et == ExecType.SPARK )
				{
					IndexingMethod method = optFindIndexingMethod( _rowLowerEqualsUpper, _colLowerEqualsUpper,
                            input._dim1, input._dim2, _dim1, _dim2);
					SparkAggType aggtype = (method==IndexingMethod.MR_VRIX || isBlockAligned()) ? 
							SparkAggType.NONE : SparkAggType.MULTI_BLOCK;
					
					Lop dummy = Data.createLiteralLop(ValueType.INT, Integer.toString(-1));
					RightIndex reindex = new RightIndex(
							input.constructLops(), getInput().get(1).constructLops(), getInput().get(2).constructLops(),
							getInput().get(3).constructLops(), getInput().get(4).constructLops(), dummy, dummy,
							getDataType(), getValueType(), aggtype, et);
				
					setOutputDimensions(reindex);
					setLineNumbers(reindex);
					setLops(reindex);
				}
				else //CP or GPU
				{
					Lop dummy = Data.createLiteralLop(ValueType.INT, Integer.toString(-1));
					RightIndex reindex = new RightIndex(
							input.constructLops(), getInput().get(1).constructLops(), getInput().get(2).constructLops(),
							getInput().get(3).constructLops(), getInput().get(4).constructLops(), dummy, dummy,
							getDataType(), getValueType(), et);
					
					setOutputDimensions(reindex);
					setLineNumbers(reindex);
					setLops(reindex);
				}
			} catch (Exception e) {
				throw new HopsException(this.printErrorLocation() + "In IndexingOp Hop, error constructing Lops " , e);
			}
		}
		
		//add reblock/checkpoint lops if necessary
		constructAndSetLopsDataFlowProperties();
		
		return getLops();
	}

	@Override
	public String getOpString() {
		String s = new String("");
		s += OPSTRING;
		return s;
	}
	
	@Override
	public boolean allowsAllExecTypes()
	{
		return true;
	}
	
	@Override
	public void computeMemEstimate( MemoTable memo )
	{
		//default behavior
		super.computeMemEstimate(memo);
		
		//try to infer via worstcase input statistics (for the case of dims known
		//but nnz initially unknown)
		MatrixCharacteristics mcM1 = memo.getAllInputStats(getInput().get(0));
		if( dimsKnown() && mcM1.getNonZeros()>=0 ){
			long lnnz = mcM1.getNonZeros(); //worst-case output nnz
			double lOutMemEst = computeOutputMemEstimate( _dim1, _dim2, lnnz );
			if( lOutMemEst<_outputMemEstimate ){
				_outputMemEstimate = lOutMemEst;
				_memEstimate = getInputOutputSize();				
			}
		}		
	}
	
	@Override
	protected double computeOutputMemEstimate( long dim1, long dim2, long nnz )
	{		
		// only dense right indexing supported on GPU
		double sparsity =  isGPUEnabled() ? 1.0 : OptimizerUtils.getSparsity(dim1, dim2, nnz);
		return OptimizerUtils.estimateSizeExactSparsity(dim1, dim2, sparsity);
	}
	
	@Override
	protected double computeIntermediateMemEstimate( long dim1, long dim2, long nnz )
	{
		return 0;
	}
	
	@Override
	protected long[] inferOutputCharacteristics( MemoTable memo )
	{
		long[] ret = null;
		
		Hop input = getInput().get(0); //original matrix
		MatrixCharacteristics mc = memo.getAllInputStats(input);
		if( mc != null ) 
		{
			long lnnz = mc.dimsKnown()?Math.min(mc.getRows()*mc.getCols(), mc.getNonZeros()):-1;
			//worst-case is input size, but dense
			ret = new long[]{mc.getRows(), mc.getCols(), lnnz};
			
			//exploit column/row indexing information
			if( _rowLowerEqualsUpper ) ret[0]=1;
			if( _colLowerEqualsUpper ) ret[1]=1;	
			
			//infer tight block indexing size
			Hop rl = getInput().get(1);
			Hop ru = getInput().get(2);
			Hop cl = getInput().get(3);
			Hop cu = getInput().get(4);
			if( isBlockIndexingExpression(rl, ru) )
				ret[0] = getBlockIndexingExpressionSize(rl, ru);
			if( isBlockIndexingExpression(cl, cu) )
				ret[1] = getBlockIndexingExpressionSize(cl, cu);
		}
		
		return ret;
	}
	
	/**
	 * Indicates if the lbound:rbound expressions is of the form
	 * "(c * (i - 1) + 1) : (c * i)", where we could use c as a tight size estimate.
	 * 
	 * @param lbound lower bound high-level operator
	 * @param ubound uppser bound high-level operator
	 * @return true if block indexing expression
	 */
	private static boolean isBlockIndexingExpression(Hop lbound, Hop ubound) 
	{
		boolean ret = false;
		LiteralOp constant = null;
		DataOp var = null;

		//handle lower bound
		if( lbound instanceof BinaryOp && ((BinaryOp)lbound).getOp()==OpOp2.PLUS
			&& lbound.getInput().get(1) instanceof LiteralOp 
			&& HopRewriteUtils.getDoubleValueSafe((LiteralOp)lbound.getInput().get(1))==1
			&& lbound.getInput().get(0) instanceof BinaryOp)
		{
			BinaryOp lmult = (BinaryOp)lbound.getInput().get(0);
			if( lmult.getOp()==OpOp2.MULT && lmult.getInput().get(0) instanceof LiteralOp
				&& lmult.getInput().get(1) instanceof BinaryOp )
			{
				BinaryOp lminus = (BinaryOp)lmult.getInput().get(1);
				if( lminus.getOp()==OpOp2.MINUS && lminus.getInput().get(1) instanceof LiteralOp
					&& HopRewriteUtils.getDoubleValueSafe((LiteralOp)lminus.getInput().get(1))==1 
					&& lminus.getInput().get(0) instanceof DataOp )
				{
					constant = (LiteralOp)lmult.getInput().get(0);
					var = (DataOp) lminus.getInput().get(0);
				}
			}
		}
		
		//handle upper bound
		if( var != null && constant != null && ubound instanceof BinaryOp 
			&& ubound.getInput().get(0) instanceof LiteralOp
			&& ubound.getInput().get(1) instanceof DataOp 
			&& ubound.getInput().get(1).getName().equals(var.getName()) ) 
		{
			LiteralOp constant2 = (LiteralOp)ubound.getInput().get(0);
			ret = ( HopRewriteUtils.getDoubleValueSafe(constant) == 
					HopRewriteUtils.getDoubleValueSafe(constant2) );
		}
		
		return ret;
	}
	
	/**
	 * Indicates if the right indexing ranging is block aligned, i.e., it does not require
	 * aggregation across blocks due to shifting.
	 * 
	 * @return true if block aligned
	 */
	private boolean isBlockAligned() {
		Hop input1 = getInput().get(0); //original matrix
		Hop input2 = getInput().get(1); //inpRowL
		Hop input3 = getInput().get(2); //inpRowU
		Hop input4 = getInput().get(3); //inpColL
		Hop input5 = getInput().get(4); //inpRowU
		
		long rl = (input2 instanceof LiteralOp) ? (HopRewriteUtils.getIntValueSafe((LiteralOp)input2)) : -1;
		long ru = (input3 instanceof LiteralOp) ? (HopRewriteUtils.getIntValueSafe((LiteralOp)input3)) : -1;
		long cl = (input4 instanceof LiteralOp) ? (HopRewriteUtils.getIntValueSafe((LiteralOp)input4)) : -1;
		long cu = (input5 instanceof LiteralOp) ? (HopRewriteUtils.getIntValueSafe((LiteralOp)input5)) : -1;
		int brlen = (int)input1.getRowsInBlock();
		int bclen = (int)input1.getColsInBlock();
		
		return OptimizerUtils.isIndexingRangeBlockAligned(rl, ru, cl, cu, brlen, bclen);
	}

	private static long getBlockIndexingExpressionSize(Hop lbound, Hop ubound) {
		//NOTE: ensure consistency with isBlockIndexingExpression
		LiteralOp c = (LiteralOp) ubound.getInput().get(0); //(c*i)
		return HopRewriteUtils.getIntValueSafe(c);
	}

	@Override
	protected ExecType optFindExecType() throws HopsException {
		
		checkAndSetForcedPlatform();

		ExecType REMOTE = OptimizerUtils.isSparkExecutionMode() ? ExecType.SPARK : ExecType.MR;
		
		if( _etypeForced != null ) 			
		{
			_etype = _etypeForced;
		}
		else
		{
			if ( OptimizerUtils.isMemoryBasedOptLevel() ) {
				_etype = findExecTypeByMemEstimate();
			}
			else if ( getInput().get(0).areDimsBelowThreshold() )
			{
				_etype = ExecType.CP;
			}
			else
			{
				_etype = REMOTE;
			}
			
			//check for valid CP dimensions and matrix size
			checkAndSetInvalidCPDimsAndSize();
		}

		//mark for recompile (forever)
		setRequiresRecompileIfNecessary();
		
		return _etype;
	}

	private static IndexingMethod optFindIndexingMethod( boolean singleRow, boolean singleCol, long m1_dim1, long m1_dim2, long m2_dim1, long m2_dim2 )
	{
		if(    singleRow && m1_dim2 == m2_dim2 && m2_dim2!=-1
			|| singleCol && m1_dim1 == m2_dim1 && m2_dim1!=-1 )
		{
			return IndexingMethod.MR_VRIX;
		}
		
		return IndexingMethod.MR_RIX; //general case
	}
	
	@Override
	public void refreshSizeInformation()
	{
		Hop input2 = getInput().get(1); //inpRowL
		Hop input3 = getInput().get(2); //inpRowU
		Hop input4 = getInput().get(3); //inpColL
		Hop input5 = getInput().get(4); //inpColU
		
		//update single row/column flags (depends on CSE)
		_rowLowerEqualsUpper = (input2 == input3);
		_colLowerEqualsUpper = (input4 == input5);
		
		//parse input information
		boolean allRows = 
			(    input2 instanceof LiteralOp && HopRewriteUtils.getIntValueSafe((LiteralOp)input2)==1 
			  && input3 instanceof UnaryOp && ((UnaryOp)input3).getOp() == OpOp1.NROW  );
		boolean allCols = 
			(    input4 instanceof LiteralOp && HopRewriteUtils.getIntValueSafe((LiteralOp)input4)==1 
			  && input5 instanceof UnaryOp && ((UnaryOp)input5).getOp() == OpOp1.NCOL );
		boolean constRowRange = (input2 instanceof LiteralOp && input3 instanceof LiteralOp);
		boolean constColRange = (input4 instanceof LiteralOp && input5 instanceof LiteralOp);
		
		//set dimension information
		if( _rowLowerEqualsUpper ) //ROWS
			setDim1(1);
		else if( allRows ) {
			//input3 guaranteed to be a unaryop-nrow
			setDim1(input3.getInput().get(0).getDim1());
		}
		else if( constRowRange ) {
			setDim1( HopRewriteUtils.getIntValueSafe((LiteralOp)input3)
					-HopRewriteUtils.getIntValueSafe((LiteralOp)input2)+1 );
		}
		else if( isBlockIndexingExpression(input2, input3) ) {
			setDim1(getBlockIndexingExpressionSize(input2, input3));
		}
		
		if( _colLowerEqualsUpper ) //COLS
			setDim2(1);
		else if( allCols ) {
			//input5 guaranteed to be a unaryop-ncol
			setDim2(input5.getInput().get(0).getDim2());
		}
		else if( constColRange ) {
			setDim2( HopRewriteUtils.getIntValueSafe((LiteralOp)input5)
					-HopRewriteUtils.getIntValueSafe((LiteralOp)input4)+1 );
		}
		else if( isBlockIndexingExpression(input4, input5) ) {
			setDim2(getBlockIndexingExpressionSize(input4, input5));
		}
	}
	
	@Override
	public Object clone() throws CloneNotSupportedException 
	{
		IndexingOp ret = new IndexingOp();	
		
		//copy generic attributes
		ret.clone(this, false);
		
		//copy specific attributes

		return ret;
	}
	
	@Override
	public boolean compare( Hop that )
	{		
		if(    !(that instanceof IndexingOp) 
			|| getInput().size() != that.getInput().size() )
		{
			return false;
		}
		
		return (  getInput().get(0) == that.getInput().get(0)
				&& getInput().get(1) == that.getInput().get(1)
				&& getInput().get(2) == that.getInput().get(2)
				&& getInput().get(3) == that.getInput().get(3)
				&& getInput().get(4) == that.getInput().get(4));
	}
}

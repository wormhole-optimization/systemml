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
import org.apache.sysml.api.DMLScript.RUNTIME_PLATFORM;
import org.apache.sysml.hops.Hop.MultiThreadedHop;
import org.apache.sysml.hops.rewrite.HopRewriteUtils;
import org.apache.sysml.lops.Aggregate;
import org.apache.sysml.lops.Binary;
import org.apache.sysml.lops.DataPartition;
import org.apache.sysml.lops.Group;
import org.apache.sysml.lops.Lop;
import org.apache.sysml.lops.LopProperties.ExecType;
import org.apache.sysml.lops.LopsException;
import org.apache.sysml.lops.MMCJ;
import org.apache.sysml.lops.MMCJ.MMCJType;
import org.apache.sysml.lops.MMRJ;
import org.apache.sysml.lops.MMTSJ;
import org.apache.sysml.lops.MMTSJ.MMTSJType;
import org.apache.sysml.lops.MMZip;
import org.apache.sysml.lops.MapMult;
import org.apache.sysml.lops.MapMultChain;
import org.apache.sysml.lops.MapMultChain.ChainType;
import org.apache.sysml.lops.PMMJ;
import org.apache.sysml.lops.PMapMult;
import org.apache.sysml.lops.PartialAggregate.CorrectionLocationType;
import org.apache.sysml.lops.Transform;
import org.apache.sysml.lops.Transform.OperationTypes;
import org.apache.sysml.parser.Expression.DataType;
import org.apache.sysml.parser.Expression.ValueType;
import org.apache.sysml.runtime.controlprogram.ParForProgramBlock.PDataPartitionFormat;
import org.apache.sysml.runtime.controlprogram.context.SparkExecutionContext;
import org.apache.sysml.runtime.matrix.MatrixCharacteristics;
import org.apache.sysml.runtime.matrix.data.MatrixBlock;
import org.apache.sysml.runtime.matrix.mapred.DistributedCacheInput;
import org.apache.sysml.runtime.matrix.mapred.MMCJMRReducerWithAggregator;


/* Aggregate binary (cell operations): Sum (aij + bij)
 * 		Properties: 
 * 			Inner Symbol: *, -, +, ...
 * 			Outer Symbol: +, min, max, ...
 * 			2 Operands
 * 	
 * 		Semantic: generate indices, align, cross-operate, generate indices, align, aggregate
 */

public class AggBinaryOp extends Hop implements MultiThreadedHop
{
	public static final double MAPMULT_MEM_MULTIPLIER = 1.0;
	public static MMultMethod FORCED_MMULT_METHOD = null;

	public enum MMultMethod { 
		CPMM,     //cross-product matrix multiplication (mr)
		RMM,      //replication matrix multiplication (mr)
		MAPMM_L,  //map-side matrix-matrix multiplication using distributed cache (mr/sp)
		MAPMM_R,  //map-side matrix-matrix multiplication using distributed cache (mr/sp)
		MAPMM_CHAIN, //map-side matrix-matrix-matrix multiplication using distributed cache, for right input (cp/mr/sp)
		PMAPMM,   //partitioned map-side matrix-matrix multiplication (sp)
		PMM,      //permutation matrix multiplication using distributed cache, for left input (mr/cp)
		TSMM,     //transpose-self matrix multiplication (cp/mr/sp)
		TSMM2,    //transpose-self matrix multiplication, 2-pass w/o shuffle (sp)
		ZIPMM,    //zip matrix multiplication (sp)
		MM        //in-memory matrix multiplication (cp)
	}
	
	public enum SparkAggType{
		NONE,
		SINGLE_BLOCK,
		MULTI_BLOCK,
	}
	
	public final OpOp2 innerOp;
	public final AggOp outerOp;

	private MMultMethod _method = null;
	
	//hints set by previous to operator selection
	private boolean _hasLeftPMInput = false; //left input is permutation matrix
	private int _maxNumThreads = -1; //-1 for unlimited
	
	private AggBinaryOp(OpOp2 innerOp, AggOp outerOp) {
		//default constructor for clone
		this.innerOp = innerOp;
		this.outerOp = outerOp;
	}
	
	public AggBinaryOp(String l, DataType dt, ValueType vt, OpOp2 innOp,
			AggOp outOp, Hop in1, Hop in2) {
		super(l, dt, vt);
		innerOp = innOp;
		outerOp = outOp;
		getInput().add(0, in1);
		getInput().add(1, in2);
		in1.getParent().add(this);
		in2.getParent().add(this);
		
		//compute unknown dims and nnz
		refreshSizeInformation();
	}

	@Override
	public void checkArity() throws HopsException {
		HopsException.check(_input.size() == 2, this, "should have arity 2 but has arity %d", _input.size());
	}

	public void setHasLeftPMInput(boolean flag) {
		_hasLeftPMInput = flag;
	}
	
	public boolean hasLeftPMInput(){
		return _hasLeftPMInput;
	}

	@Override
	public void setMaxNumThreads( int k ) {
		_maxNumThreads = k;
	}
	
	@Override
	public int getMaxNumThreads() {
		return _maxNumThreads;
	}
	
	public MMultMethod getMMultMethod(){
		return _method;
	}
	
	@Override
	public boolean isGPUEnabled() {
		if(!DMLScript.USE_ACCELERATOR)
			return false;
		
		Hop input1 = getInput().get(0);
		Hop input2 = getInput().get(1);
		//matrix mult operation selection part 2 (specific pattern)
		MMTSJType mmtsj = checkTransposeSelf(); //determine tsmm pattern
		ChainType chain = checkMapMultChain(); //determine mmchain pattern
		
		_method = optFindMMultMethodCP ( input1.getDim1(), input1.getDim2(),   
			      input2.getDim1(), input2.getDim2(), mmtsj, chain, _hasLeftPMInput );
		switch( _method ){
			case TSMM: 
				return true;
			case MAPMM_CHAIN:
				return false;
			case PMM:
				return false;
			case MM:
				return true;
			default:
				throw new RuntimeException("Unsupported method:" + _method);
		}
	}
	
	/**
	 * NOTE: overestimated mem in case of transpose-identity matmult, but 3/2 at worst
	 *       and existing mem estimate advantageous in terms of consistency hops/lops,
	 *       and some special cases internally materialize the transpose for better cache locality  
	 */
	@Override
	public Lop constructLops() 
		throws HopsException, LopsException
	{
		//return already created lops
		if( getLops() != null )
			return getLops();
	
		//construct matrix mult lops (currently only supported aggbinary)
		if ( isMatrixMultiply() ) 
		{
			Hop input1 = getInput().get(0);
			Hop input2 = getInput().get(1);
			
			//matrix mult operation selection part 1 (CP vs MR vs Spark)
			ExecType et = optFindExecType();
			
			//matrix mult operation selection part 2 (specific pattern)
			MMTSJType mmtsj = checkTransposeSelf(); //determine tsmm pattern
			ChainType chain = checkMapMultChain(); //determine mmchain pattern
			
			if( et == ExecType.CP || et == ExecType.GPU ) 
			{
				//matrix mult operation selection part 3 (CP type)
				_method = optFindMMultMethodCP ( input1.getDim1(), input1.getDim2(),   
						      input2.getDim1(), input2.getDim2(), mmtsj, chain, _hasLeftPMInput );
				
				//dispatch CP lops construction 
				switch( _method ){
					case TSMM: 
						constructCPLopsTSMM( mmtsj, et );
						break;
					case MAPMM_CHAIN:
						constructCPLopsMMChain( chain );
						break;
					case PMM:
						constructCPLopsPMM();
						break;
					case MM:
						constructCPLopsMM(et);
						break;
					default:
						throw new HopsException(this.printErrorLocation() + "Invalid Matrix Mult Method (" + _method + ") while constructing CP lops.");
				}
			}
			else if( et == ExecType.SPARK ) 
			{
				//matrix mult operation selection part 3 (SPARK type)
				boolean tmmRewrite = HopRewriteUtils.isTransposeOperation(input1);
				_method = optFindMMultMethodSpark ( 
						input1.getDim1(), input1.getDim2(), input1.getRowsInBlock(), input1.getColsInBlock(), input1.getNnz(),   
						input2.getDim1(), input2.getDim2(), input2.getRowsInBlock(), input2.getColsInBlock(), input2.getNnz(),
						mmtsj, chain, _hasLeftPMInput, tmmRewrite );
			
				//dispatch SPARK lops construction 
				switch( _method )
				{
					case TSMM:
					case TSMM2:	
						constructSparkLopsTSMM( mmtsj, _method==MMultMethod.TSMM2 );
						break;
					case MAPMM_L:
					case MAPMM_R:
						constructSparkLopsMapMM( _method );
						break;
					case MAPMM_CHAIN:
						constructSparkLopsMapMMChain( chain );
						break;
					case PMAPMM:
						constructSparkLopsPMapMM();
						break;
					case CPMM:	
						constructSparkLopsCPMM();
						break;
					case RMM:	
						constructSparkLopsRMM();
						break;
					case PMM:
						constructSparkLopsPMM(); 
						break;
					case ZIPMM:
						constructSparkLopsZIPMM(); 
						break;
						
					default:
						throw new HopsException(this.printErrorLocation() + "Invalid Matrix Mult Method (" + _method + ") while constructing SPARK lops.");	
				}
			}
			else if( et == ExecType.MR ) 
			{
				//matrix mult operation selection part 3 (MR type)
				_method = optFindMMultMethodMR ( 
							input1.getDim1(), input1.getDim2(), input1.getRowsInBlock(), input1.getColsInBlock(), input1.getNnz(),    
							input2.getDim1(), input2.getDim2(), input2.getRowsInBlock(), input2.getColsInBlock(), input2.getNnz(),
							mmtsj, chain, _hasLeftPMInput);
			
				//dispatch MR lops construction
				switch( _method ) {
					case MAPMM_L:
					case MAPMM_R: 	
						constructMRLopsMapMM( _method ); 
						break;
					case MAPMM_CHAIN:	
						constructMRLopsMapMMChain( chain ); 
						break;
					case CPMM:
						constructMRLopsCPMM(); 
						break;
					case RMM:			
						constructMRLopsRMM();
						break;
					case TSMM:
						constructMRLopsTSMM( mmtsj ); 
						break;
					case PMM:
						constructMRLopsPMM(); 
						break;						
					default:
						throw new HopsException(this.printErrorLocation() + "Invalid Matrix Mult Method (" + _method + ") while constructing MR lops.");
				}
			}
		} 
		else
			throw new HopsException(this.printErrorLocation() + "Invalid operation in AggBinary Hop, aggBin(" + innerOp + "," + outerOp + ") while constructing lops.");
		
		//add reblock/checkpoint lops if necessary
		constructAndSetLopsDataFlowProperties();
		
		return getLops();
	}

	@Override
	public String getOpString() {
		//ba - binary aggregate, for consistency with runtime 
		String s = "ba(" + 
				HopsAgg2String.get(outerOp) + 
				HopsOpOp2String.get(innerOp)+")";
		return s;
	}
	
	@Override
	public void computeMemEstimate(MemoTable memo) 
	{
		//extension of default compute memory estimate in order to 
		//account for smaller tsmm memory requirements.
		super.computeMemEstimate(memo);
		
		//tsmm left is guaranteed to require only X but not t(X), while
		//tsmm right might have additional requirements to transpose X if sparse
		//NOTE: as a heuristic this correction is only applied if not a column vector because
		//most other vector operations require memory for at least two vectors (we aim for 
		//consistency in order to prevent anomalies in parfor opt leading to small degree of par)
		MMTSJType mmtsj = checkTransposeSelf();
		if( mmtsj.isLeft() && getInput().get(1).dimsKnown() && getInput().get(1).getDim2()>1 ) {
			_memEstimate = _memEstimate - getInput().get(0)._outputMemEstimate;
		}
	}

	@Override
	protected double computeOutputMemEstimate( long dim1, long dim2, long nnz )
	{		
		//NOTES:  
		// * The estimate for transpose-self is the same as for normal matrix multiplications
		//   because (1) this decouples the decision of TSMM over default MM and (2) some cases
		//   of TSMM internally materialize the transpose for efficiency.
		// * All matrix multiplications internally use dense output representations for efficiency.
		//   This is reflected in our conservative memory estimate. However, we additionally need 
		//   to account for potential final dense/sparse transformations via processing mem estimates.
		double sparsity = 1.0;
		/*
		if( isMatrixMultiply() ) {	
			if( nnz < 0 ){
				Hops input1 = getInput().get(0);
				Hops input2 = getInput().get(1);
				if( input1.dimsKnown() && input2.dimsKnown() )
				{
					double sp1 = (input1.getNnz()>0) ? OptimizerUtils.getSparsity(input1.getDim1(), input1.getDim2(), input1.getNnz()) : 1.0;
					double sp2 = (input2.getNnz()>0) ? OptimizerUtils.getSparsity(input2.getDim1(), input2.getDim2(), input2.getNnz()) : 1.0;
					sparsity = OptimizerUtils.getMatMultSparsity(sp1, sp2, input1.getDim1(), input1.getDim2(), input2.getDim2(), true);	
				}
			}
			else //sparsity known (e.g., inferred from worst case estimates)
				sparsity = OptimizerUtils.getSparsity(dim1, dim2, nnz);
		}
		*/
		//currently always estimated as dense in order to account for dense intermediate without unnecessary overestimation 
		double ret = OptimizerUtils.estimateSizeExactSparsity(dim1, dim2, sparsity);
		
		return ret;
	}
	
	@Override
	protected double computeIntermediateMemEstimate( long dim1, long dim2, long nnz )
	{
		double ret = 0;

		if (isGPUEnabled()) {
			// In GPU Mode, intermediate memory is only needed in case of one of the matrix blocks is sparse
			// When sparse block is converted to dense and a dense MM takes place, we need (dim1 * dim2)
			// When dense block is converted to sparse and a sparse MM takes place, we need (dim1 * dim2 * 2)

			Hop in1 = _input.get(0);
			Hop in2 = _input.get(1);
			double in1Sparsity = OptimizerUtils.getSparsity(in1.getDim1(), in1.getDim2(), in1.getNnz());
			double in2Sparsity = OptimizerUtils.getSparsity(in2.getDim1(), in2.getDim2(), in2.getNnz());

			boolean in1Sparse = in1Sparsity < MatrixBlock.SPARSITY_TURN_POINT;
			boolean in2Sparse = in2Sparsity < MatrixBlock.SPARSITY_TURN_POINT;

			boolean in1UltraSparse = in1Sparsity < MatrixBlock.ULTRA_SPARSITY_TURN_POINT;
			boolean in2UltraSparse = in2Sparsity < MatrixBlock.ULTRA_SPARSITY_TURN_POINT;

			// For Matmult X * Y, if X is sparse, Y is dense, X is converted to dense
			// If X is ultrasparse, Y is converted to sparse
			if (in1Sparse ^ in2Sparse) { // one sparse, one dense
				if (in1Sparse) {
					if (in1UltraSparse) {
						ret += 2 * OptimizerUtils.estimateSizeExactSparsity(in2.getDim1(), in2.getDim2(), in2.getNnz());
					} else {
						ret += OptimizerUtils.estimateSizeExactSparsity(in1.getDim1(), in1.getDim2(), in1.getNnz());
					}
				} else if (in2Sparse) {
					if (in2UltraSparse) {
						ret += 2 * OptimizerUtils.estimateSizeExactSparsity(in1.getDim1(), in1.getDim2(), in1.getNnz());
					} else {
						ret += OptimizerUtils.estimateSizeExactSparsity(in2.getDim1(), in2.getDim2(), in2.getNnz());
					}
				}

			}

		}

		//account for potential final dense-sparse transformation (worst-case sparse representation)
		if( dim2 >= 2 ) //vectors always dense
			ret += OptimizerUtils.estimateSizeExactSparsity(dim1, dim2, MatrixBlock.SPARSITY_TURN_POINT);

		return ret;
	}
	
	@Override
	protected long[] inferOutputCharacteristics( MemoTable memo )
	{
		long[] ret = null;
	
		MatrixCharacteristics[] mc = memo.getAllInputStats(getInput());
		if( mc[0].rowsKnown() && mc[1].colsKnown() ) {
			ret = new long[3];
			ret[0] = mc[0].getRows();
			ret[1] = mc[1].getCols();
			double sp1 = (mc[0].getNonZeros()>0) ? OptimizerUtils.getSparsity(mc[0].getRows(), mc[0].getCols(), mc[0].getNonZeros()) : 1.0; 
			double sp2 = (mc[1].getNonZeros()>0) ? OptimizerUtils.getSparsity(mc[1].getRows(), mc[1].getCols(), mc[1].getNonZeros()) : 1.0; 			
			ret[2] = (long) ( ret[0] * ret[1] * OptimizerUtils.getMatMultSparsity(sp1, sp2, ret[0], mc[0].getCols(), ret[1], true));
		}
		
		return ret;
	}
	

	public boolean isMatrixMultiply() {
		return ( this.innerOp == OpOp2.MULT && this.outerOp == AggOp.SUM );			
	}
	
	private boolean isOuterProduct() {
		if ( getInput().get(0).isVector() && getInput().get(1).isVector() ) {
			if ( getInput().get(0).getDim1() == 1 && getInput().get(0).getDim1() > 1
					&& getInput().get(1).getDim1() > 1 && getInput().get(1).getDim2() == 1 )
				return true;
			else
				return false;
		}
		return false;
	}
	
	@Override
	public boolean allowsAllExecTypes()
	{
		return true;
	}
	
	@Override
	protected ExecType optFindExecType() 
		throws HopsException 
	{	
		checkAndSetForcedPlatform();

		ExecType REMOTE = OptimizerUtils.isSparkExecutionMode() ? ExecType.SPARK : ExecType.MR;
		
		if( _etypeForced != null ) 			
		{
			_etype = _etypeForced;
		}
		else 
		{
			if ( OptimizerUtils.isMemoryBasedOptLevel() ) 
			{
				_etype = findExecTypeByMemEstimate();
			}
			// choose CP if the dimensions of both inputs are below Hops.CPThreshold 
			// OR if it is vector-vector inner product
			else if ( (getInput().get(0).areDimsBelowThreshold() && getInput().get(1).areDimsBelowThreshold())
						|| (getInput().get(0).isVector() && getInput().get(1).isVector() && !isOuterProduct()) )
			{
				_etype = ExecType.CP;
			}
			else
			{
				_etype = REMOTE;
			}
			
			//check for valid CP mmchain, send invalid memory requirements to remote
			if( _etype == ExecType.CP && checkMapMultChain() != ChainType.NONE
				&& OptimizerUtils.getLocalMemBudget() < 
				getInput().get(0).getInput().get(0).getOutputMemEstimate() )
				_etype = REMOTE;
			
			//check for valid CP dimensions and matrix size
			checkAndSetInvalidCPDimsAndSize();
		}
		
		//spark-specific decision refinement (execute binary aggregate w/ left or right spark input and 
		//single parent also in spark because it's likely cheap and reduces data transfer)
		if( _etype == ExecType.CP && _etypeForced != ExecType.CP &&
			(isApplicableForTransitiveSparkExecType(true) || isApplicableForTransitiveSparkExecType(false)) )    
		{
			//pull binary aggregate into spark 
			_etype = ExecType.SPARK;
		}
		
		//mark for recompile (forever)
		setRequiresRecompileIfNecessary();
		
		return _etype;
	}
	
	private boolean isApplicableForTransitiveSparkExecType(boolean left) 
		throws HopsException 
	{
		int index = left ? 0 : 1;
		return !(getInput().get(index) instanceof DataOp && ((DataOp)getInput().get(index)).requiresCheckpoint())  
			&& !HopRewriteUtils.isTransposeOperation(getInput().get(index))
			&& getInput().get(index).getParent().size()==1 //bagg is only parent	
			&& !getInput().get(index).areDimsBelowThreshold() 
			&& getInput().get(index).optFindExecType() == ExecType.SPARK
			&& getInput().get(index).getOutputMemEstimate()>getOutputMemEstimate();
	}
	
	/**
	 * TSMM: Determine if XtX pattern applies for this aggbinary and if yes
	 * which type. 
	 * 
	 * @return MMTSJType
	 */
	public MMTSJType checkTransposeSelf()
	{
		MMTSJType ret = MMTSJType.NONE;
		
		Hop in1 = getInput().get(0);
		Hop in2 = getInput().get(1);
		
		if( HopRewriteUtils.isTransposeOperation(in1)
			&& in1.getInput().get(0) == in2 )
		{
			ret = MMTSJType.LEFT;
		}
		
		if( HopRewriteUtils.isTransposeOperation(in2) 
			&& in2.getInput().get(0) == in1 )
		{
			ret = MMTSJType.RIGHT;
		}
		
		return ret;
	}

	/**
	 * MapMultChain: Determine if XtwXv/XtXv pattern applies for this aggbinary 
	 * and if yes which type. 
	 * 
	 * @return ChainType
	 */
	public ChainType checkMapMultChain()
	{
		ChainType chainType = ChainType.NONE;
		
		Hop in1 = getInput().get(0);
		Hop in2 = getInput().get(1);
		
		//check for transpose left input (both chain types)
		if( HopRewriteUtils.isTransposeOperation(in1) )
		{
			Hop X = in1.getInput().get(0);
				
			//check mapmultchain patterns
			//t(X)%*%(w*(X%*%v))
			if( in2 instanceof BinaryOp && ((BinaryOp)in2).getOp()==OpOp2.MULT )
			{
				Hop in3b = in2.getInput().get(1);
				if( in3b instanceof AggBinaryOp )
				{
					Hop in4 = in3b.getInput().get(0);
					if( X == in4 ) //common input
						chainType = ChainType.XtwXv;
				}
			}
			//t(X)%*%((X%*%v)-y)
			else if( in2 instanceof BinaryOp && ((BinaryOp)in2).getOp()==OpOp2.MINUS )
			{
				Hop in3a = in2.getInput().get(0);
				Hop in3b = in2.getInput().get(1);				
				if( in3a instanceof AggBinaryOp && in3b.getDataType()==DataType.MATRIX )
				{
					Hop in4 = in3a.getInput().get(0);
					if( X == in4 ) //common input
						chainType = ChainType.XtXvy;
				}
			}
			//t(X)%*%(X%*%v)
			else if( in2 instanceof AggBinaryOp )
			{
				Hop in3 = in2.getInput().get(0);
				if( X == in3 ) //common input
					chainType = ChainType.XtXv;
			}
		}
		
		return chainType;
	}
	
	//////////////////////////
	// CP Lops generation
	/////////////////////////
	
	private void constructCPLopsTSMM( MMTSJType mmtsj, ExecType et ) 
		throws HopsException, LopsException
	{
		int k = OptimizerUtils.getConstrainedNumThreads(_maxNumThreads);
		
		Lop matmultCP = new MMTSJ(getInput().get(mmtsj.isLeft()?1:0).constructLops(),
				                 getDataType(), getValueType(), et, mmtsj, false, k);
	
		matmultCP.getOutputParameters().setDimensions(getDim1(), getDim2(), getRowsInBlock(), getColsInBlock(), getNnz());
		setLineNumbers( matmultCP );
		setLops(matmultCP);
	}

	private void constructCPLopsMMChain( ChainType chain ) 
		throws LopsException, HopsException
	{
		MapMultChain mapmmchain = null;
		if( chain == ChainType.XtXv ) {
			Hop hX = getInput().get(0).getInput().get(0);
			Hop hv = getInput().get(1).getInput().get(1);
			mapmmchain = new MapMultChain( hX.constructLops(), hv.constructLops(), getDataType(), getValueType(), ExecType.CP);
		}
		else { //ChainType.XtwXv / ChainType.XtwXvy
			int wix = (chain == ChainType.XtwXv) ? 0 : 1;
			int vix = (chain == ChainType.XtwXv) ? 1 : 0;
			Hop hX = getInput().get(0).getInput().get(0);
			Hop hw = getInput().get(1).getInput().get(wix);
			Hop hv = getInput().get(1).getInput().get(vix).getInput().get(1);
			mapmmchain = new MapMultChain( hX.constructLops(), hv.constructLops(), hw.constructLops(), chain, getDataType(), getValueType(), ExecType.CP);
		}
		
		//set degree of parallelism
		int k = OptimizerUtils.getConstrainedNumThreads(_maxNumThreads);
		mapmmchain.setNumThreads( k );
		
		//set basic lop properties
		setOutputDimensions(mapmmchain);
		setLineNumbers(mapmmchain);
		setLops(mapmmchain);
	}
	
	/**
	 * NOTE: exists for consistency since removeEmtpy might be scheduled to MR
	 * but matrix mult on small output might be scheduled to CP. Hence, we 
	 * need to handle directly passed selection vectors in CP as well.
	 * 
	 * @throws HopsException if HopsException occurs
	 * @throws LopsException if LopsException occurs
	 */
	private void constructCPLopsPMM() 
		throws HopsException, LopsException
	{
		Hop pmInput = getInput().get(0);
		Hop rightInput = getInput().get(1);
		
		Hop nrow = HopRewriteUtils.createValueHop(pmInput, true); //NROW
		nrow.setOutputBlocksizes(0, 0);
		nrow.setForcedExecType(ExecType.CP);
		HopRewriteUtils.copyLineNumbers(this, nrow);
		Lop lnrow = nrow.constructLops();
		
		PMMJ pmm = new PMMJ(pmInput.constructLops(), rightInput.constructLops(), lnrow, getDataType(), getValueType(), false, false, ExecType.CP);
		
		//set degree of parallelism
		int k = OptimizerUtils.getConstrainedNumThreads(_maxNumThreads);
		pmm.setNumThreads(k);
		
		pmm.getOutputParameters().setDimensions(getDim1(), getDim2(), getRowsInBlock(), getColsInBlock(), getNnz());
		setLineNumbers(pmm);
		
		setLops(pmm);
		
		HopRewriteUtils.removeChildReference(pmInput, nrow);
	}

	private void constructCPLopsMM(ExecType et) 
		throws HopsException, LopsException
	{	
		Lop matmultCP = null;

		if (et == ExecType.GPU) {
			Hop h1 = getInput().get(0);
			Hop h2 = getInput().get(1);
			Lop left; Lop right;
			boolean isLeftTransposed; boolean isRightTransposed;
			if( HopRewriteUtils.isTransposeOperation(h1) ) {
				isLeftTransposed = true;
				left = h1.getInput().get(0).constructLops();
			}
			else {
				isLeftTransposed = false;
				left = h1.constructLops();
			}
			if( HopRewriteUtils.isTransposeOperation(h2) ) {
				isRightTransposed = true;
				right = h2.getInput().get(0).constructLops();
			}
			else {
				isRightTransposed = false;
				right = h2.constructLops();
			}
			
			matmultCP = new Binary(left, right, 
									 Binary.OperationTypes.MATMULT, getDataType(), getValueType(), et, isLeftTransposed, isRightTransposed);
			setOutputDimensions(matmultCP);
			setNnz(-1);
		}
		else {
			if( isLeftTransposeRewriteApplicable(true, false) ) {
				matmultCP = constructCPLopsMMWithLeftTransposeRewrite();
			}
			else { 
				int k = OptimizerUtils.getConstrainedNumThreads(_maxNumThreads);
				matmultCP = new Binary(getInput().get(0).constructLops(),getInput().get(1).constructLops(), 
										 Binary.OperationTypes.MATMULT, getDataType(), getValueType(), et, k);
			}
			setOutputDimensions(matmultCP);
		}
		
		setLineNumbers( matmultCP );
		setLops(matmultCP);
	}

	private Lop constructCPLopsMMWithLeftTransposeRewrite() 
		throws HopsException, LopsException
	{
		Hop X = getInput().get(0).getInput().get(0); //guaranteed to exists
		Hop Y = getInput().get(1);
		int k = OptimizerUtils.getConstrainedNumThreads(_maxNumThreads);
		
		//right vector transpose
		Lop lY = Y.constructLops();
		Lop tY = (lY instanceof Transform && ((Transform)lY).getOperationType()==OperationTypes.Transpose ) ?
				lY.getInputs().get(0) : //if input is already a transpose, avoid redundant transpose ops
				new Transform(lY, OperationTypes.Transpose, getDataType(), getValueType(), ExecType.CP, k);
		tY.getOutputParameters().setDimensions(Y.getDim2(), Y.getDim1(), getRowsInBlock(), getColsInBlock(), Y.getNnz());
		setLineNumbers(tY);
		
		//matrix mult
		Lop mult = new Binary(tY, X.constructLops(), Binary.OperationTypes.MATMULT, getDataType(), getValueType(), ExecType.CP, k);	
		mult.getOutputParameters().setDimensions(Y.getDim2(), X.getDim2(), getRowsInBlock(), getColsInBlock(), getNnz());
		setLineNumbers(mult);
		
		//result transpose (dimensions set outside)
		Lop out = new Transform(mult, OperationTypes.Transpose, getDataType(), getValueType(), ExecType.CP, k);
		
		return out;
	}
	
	//////////////////////////
	// Spark Lops generation
	/////////////////////////

	private void constructSparkLopsTSMM(MMTSJType mmtsj, boolean multiPass) 
		throws HopsException, LopsException
	{
		Hop input = getInput().get(mmtsj.isLeft()?1:0);
		MMTSJ tsmm = new MMTSJ(input.constructLops(), getDataType(), 
				getValueType(), ExecType.SPARK, mmtsj, multiPass);
		setOutputDimensions(tsmm);
		setLineNumbers(tsmm);
		setLops(tsmm);
	}

	private void constructSparkLopsMapMM(MMultMethod method) 
		throws LopsException, HopsException
	{
		Lop mapmult = null;
		if( isLeftTransposeRewriteApplicable(false, false) ) 
		{
			mapmult = constructSparkLopsMapMMWithLeftTransposeRewrite();
		}
		else
		{
			// If number of columns is smaller than block size then explicit aggregation is not required.
			// i.e., entire matrix multiplication can be performed in the mappers.
			boolean needAgg = requiresAggregation(method); 
			SparkAggType aggtype = getSparkMMAggregationType(needAgg);
			_outputEmptyBlocks = !OptimizerUtils.allowsToFilterEmptyBlockOutputs(this); 
			
			//core matrix mult
			mapmult = new MapMult( getInput().get(0).constructLops(), getInput().get(1).constructLops(), 
					                getDataType(), getValueType(), (method==MMultMethod.MAPMM_R), false, 
					                _outputEmptyBlocks, aggtype);	
		}
		setOutputDimensions(mapmult);
		setLineNumbers(mapmult);
		setLops(mapmult);	
	}

	private Lop constructSparkLopsMapMMWithLeftTransposeRewrite() 
		throws HopsException, LopsException
	{
		Hop X = getInput().get(0).getInput().get(0); //guaranteed to exists
		Hop Y = getInput().get(1);
		
		//right vector transpose
		Lop tY = new Transform(Y.constructLops(), OperationTypes.Transpose, getDataType(), getValueType(), ExecType.CP);
		tY.getOutputParameters().setDimensions(Y.getDim2(), Y.getDim1(), getRowsInBlock(), getColsInBlock(), Y.getNnz());
		setLineNumbers(tY);
		
		//matrix mult spark
		boolean needAgg = requiresAggregation(MMultMethod.MAPMM_R); 
		SparkAggType aggtype = getSparkMMAggregationType(needAgg);
		_outputEmptyBlocks = !OptimizerUtils.allowsToFilterEmptyBlockOutputs(this); 
		
		Lop mult = new MapMult( tY, X.constructLops(), getDataType(), getValueType(), 
				      false, false, _outputEmptyBlocks, aggtype);	
		mult.getOutputParameters().setDimensions(Y.getDim2(), X.getDim2(), getRowsInBlock(), getColsInBlock(), getNnz());
		setLineNumbers(mult);
		
		//result transpose (dimensions set outside)
		Lop out = new Transform(mult, OperationTypes.Transpose, getDataType(), getValueType(), ExecType.CP);
		
		return out;
	}

	private void constructSparkLopsMapMMChain(ChainType chain) 
		throws LopsException, HopsException
	{
		MapMultChain mapmmchain = null;
		if( chain == ChainType.XtXv ) {
			Hop hX = getInput().get(0).getInput().get(0);
			Hop hv = getInput().get(1).getInput().get(1);
			mapmmchain = new MapMultChain( hX.constructLops(), hv.constructLops(), getDataType(), getValueType(), ExecType.SPARK);
		}
		else { //ChainType.XtwXv / ChainType.XtXvy
			int wix = (chain == ChainType.XtwXv) ? 0 : 1;
			int vix = (chain == ChainType.XtwXv) ? 1 : 0;
			Hop hX = getInput().get(0).getInput().get(0);
			Hop hw = getInput().get(1).getInput().get(wix);
			Hop hv = getInput().get(1).getInput().get(vix).getInput().get(1);
			mapmmchain = new MapMultChain( hX.constructLops(), hv.constructLops(), hw.constructLops(), chain, getDataType(), getValueType(), ExecType.SPARK);
		}
		setOutputDimensions(mapmmchain);
		setLineNumbers(mapmmchain);
		setLops(mapmmchain);
	}

	private void constructSparkLopsPMapMM() 
		throws LopsException, HopsException
	{
		PMapMult pmapmult = new PMapMult( 
				getInput().get(0).constructLops(),
				getInput().get(1).constructLops(), 
				getDataType(), getValueType() );
		setOutputDimensions(pmapmult);
		setLineNumbers(pmapmult);
		setLops(pmapmult);
	}

	private void constructSparkLopsCPMM() 
		throws HopsException, LopsException
	{
		if( isLeftTransposeRewriteApplicable(false, false) )
		{
			setLops( constructSparkLopsCPMMWithLeftTransposeRewrite() );
		} 
		else
		{
			SparkAggType aggtype = getSparkMMAggregationType(true);
			
			Lop cpmm = new MMCJ(getInput().get(0).constructLops(), getInput().get(1).constructLops(), 
								getDataType(), getValueType(), aggtype, ExecType.SPARK);
			setOutputDimensions( cpmm );
			setLineNumbers( cpmm );
			setLops( cpmm );
		}
	}

	private Lop constructSparkLopsCPMMWithLeftTransposeRewrite() 
		throws HopsException, LopsException
	{
		SparkAggType aggtype = getSparkMMAggregationType(true);
		
		Hop X = getInput().get(0).getInput().get(0); //guaranteed to exists
		Hop Y = getInput().get(1);
		
		//right vector transpose CP
		Lop tY = new Transform(Y.constructLops(), OperationTypes.Transpose, getDataType(), getValueType(), ExecType.CP);
		tY.getOutputParameters().setDimensions(Y.getDim2(), Y.getDim1(), getRowsInBlock(), getColsInBlock(), Y.getNnz());
		setLineNumbers(tY);
		
		//matrix multiply
		MMCJ mmcj = new MMCJ(tY, X.constructLops(), getDataType(), getValueType(), aggtype, ExecType.SPARK);
		mmcj.getOutputParameters().setDimensions(getDim1(), getDim2(), getRowsInBlock(), getColsInBlock(), getNnz());
		setLineNumbers(mmcj);

		//result transpose CP 
		Lop out = new Transform(mmcj, OperationTypes.Transpose, getDataType(), getValueType(), ExecType.CP);
		out.getOutputParameters().setDimensions(X.getDim2(), Y.getDim2(), getRowsInBlock(), getColsInBlock(), getNnz());
		
		return out;
	}

	private void constructSparkLopsRMM() 
		throws LopsException, HopsException
	{
		Lop rmm = new MMRJ(getInput().get(0).constructLops(),getInput().get(1).constructLops(), 
				          getDataType(), getValueType(), ExecType.SPARK);
		setOutputDimensions(rmm);
		setLineNumbers( rmm );
		setLops(rmm);
	}

	private void constructSparkLopsPMM() 
		throws HopsException, LopsException
	{
		//PMM has two potential modes (a) w/ full permutation matrix input, and 
		//(b) w/ already condensed input vector of target row positions.
		
		Hop pmInput = getInput().get(0);
		Hop rightInput = getInput().get(1);
		
		Lop lpmInput = pmInput.constructLops();
		Hop nrow = null;
		double mestPM = OptimizerUtils.estimateSize(pmInput.getDim1(), 1);
		ExecType etVect = (mestPM>OptimizerUtils.getLocalMemBudget())?ExecType.MR:ExecType.CP;				
		
		//a) full permutation matrix input (potentially without empty block materialized)
		if( pmInput.getDim2() != 1 ) //not a vector
		{
			//compute condensed permutation matrix vector input			
			//v = rowMaxIndex(t(pm)) * rowMax(t(pm)) 
			ReorgOp transpose = HopRewriteUtils.createTranspose(pmInput);
			transpose.setForcedExecType(ExecType.SPARK);
			
			AggUnaryOp agg1 = HopRewriteUtils.createAggUnaryOp(transpose, AggOp.MAXINDEX, Direction.Row);
			agg1.setForcedExecType(ExecType.SPARK);
			
			AggUnaryOp agg2 = HopRewriteUtils.createAggUnaryOp(transpose, AggOp.MAX, Direction.Row);
			agg2.setForcedExecType(ExecType.SPARK);
			
			BinaryOp mult = HopRewriteUtils.createBinary(agg1, agg2, OpOp2.MULT);
			mult.setForcedExecType(ExecType.SPARK);
			
			//compute NROW target via nrow(m)
			nrow = HopRewriteUtils.createValueHop(pmInput, true);
			nrow.setOutputBlocksizes(0, 0);
			nrow.setForcedExecType(ExecType.CP);
			HopRewriteUtils.copyLineNumbers(this, nrow);
			
			lpmInput = mult.constructLops();
			HopRewriteUtils.removeChildReference(pmInput, transpose);
		}
		else //input vector
		{
			//compute NROW target via max(v)
			nrow = HopRewriteUtils.createAggUnaryOp(pmInput, AggOp.MAX, Direction.RowCol); 
			nrow.setOutputBlocksizes(0, 0);
			nrow.setForcedExecType(etVect);
			HopRewriteUtils.copyLineNumbers(this, nrow);
		}
		
		//b) condensed permutation matrix vector input (target rows)
		_outputEmptyBlocks = !OptimizerUtils.allowsToFilterEmptyBlockOutputs(this); 
		PMMJ pmm = new PMMJ(lpmInput, rightInput.constructLops(), nrow.constructLops(), 
				getDataType(), getValueType(), false, _outputEmptyBlocks, ExecType.SPARK);
		setOutputDimensions(pmm);
		setLineNumbers(pmm);
		setLops(pmm);
		
		HopRewriteUtils.removeChildReference(pmInput, nrow);		
	} 

	private void constructSparkLopsZIPMM() 
		throws HopsException, LopsException
	{
		//zipmm applies to t(X)%*%y if ncol(X)<=blocksize and it prevents 
		//unnecessary reshuffling by keeping the original indexes (and partitioning) 
		//joining the datasets, and internally doing the necessary transpose operations
		
		Hop left = getInput().get(0).getInput().get(0); //x out of t(X)
		Hop right = getInput().get(1); //y

		//determine left-transpose rewrite beneficial
		boolean tRewrite = (left.getDim1()*left.getDim2() >= right.getDim1()*right.getDim2());
		
		Lop zipmm = new MMZip(left.constructLops(), right.constructLops(), getDataType(), getValueType(), tRewrite, ExecType.SPARK);
		setOutputDimensions(zipmm);
		setLineNumbers( zipmm );
		setLops(zipmm);
	}
	
	//////////////////////////
	// MR Lops generation
	/////////////////////////

	private void constructMRLopsMapMM(MMultMethod method) 
		throws HopsException, LopsException
	{
		if( method == MMultMethod.MAPMM_R && isLeftTransposeRewriteApplicable(false, true) )
		{
			setLops( constructMRLopsMapMMWithLeftTransposeRewrite() );
		}
		else //GENERAL CASE
		{	
			// If number of columns is smaller than block size then explicit aggregation is not required.
			// i.e., entire matrix multiplication can be performed in the mappers.
			boolean needAgg = requiresAggregation(method); 
			boolean needPart = requiresPartitioning(method, false);
			_outputEmptyBlocks = !OptimizerUtils.allowsToFilterEmptyBlockOutputs(this); 
			
			//pre partitioning 
			Lop leftInput = getInput().get(0).constructLops(); 
			Lop rightInput = getInput().get(1).constructLops();
			if( needPart ) {
				if( (method==MMultMethod.MAPMM_L) ) //left in distributed cache
				{
					Hop input = getInput().get(0);
					ExecType etPart = (OptimizerUtils.estimateSizeExactSparsity(input.getDim1(), input.getDim2(), OptimizerUtils.getSparsity(input.getDim1(), input.getDim2(), input.getNnz())) 
					          < OptimizerUtils.getLocalMemBudget()) ? ExecType.CP : ExecType.MR; //operator selection
					leftInput = new DataPartition(input.constructLops(), DataType.MATRIX, ValueType.DOUBLE, etPart, PDataPartitionFormat.COLUMN_BLOCK_WISE_N);
					leftInput.getOutputParameters().setDimensions(input.getDim1(), input.getDim2(), getRowsInBlock(), getColsInBlock(), input.getNnz());
					setLineNumbers(leftInput);
				}
				else //right side in distributed cache
				{
					Hop input = getInput().get(1);
					ExecType etPart = (OptimizerUtils.estimateSizeExactSparsity(input.getDim1(), input.getDim2(), OptimizerUtils.getSparsity(input.getDim1(), input.getDim2(), input.getNnz())) 
					          < OptimizerUtils.getLocalMemBudget()) ? ExecType.CP : ExecType.MR; //operator selection
					rightInput = new DataPartition(input.constructLops(), DataType.MATRIX, ValueType.DOUBLE, etPart, PDataPartitionFormat.ROW_BLOCK_WISE_N);
					rightInput.getOutputParameters().setDimensions(input.getDim1(), input.getDim2(), getRowsInBlock(), getColsInBlock(), input.getNnz());
					setLineNumbers(rightInput);
				}
			}					
			
			//core matrix mult
			MapMult mapmult = new MapMult( leftInput, rightInput, getDataType(), getValueType(), 
					                (method==MMultMethod.MAPMM_R), needPart, _outputEmptyBlocks);
			mapmult.getOutputParameters().setDimensions(getDim1(), getDim2(), getRowsInBlock(), getColsInBlock(), getNnz());
			setLineNumbers(mapmult);
			
			//post aggregation
			if (needAgg) {
				Group grp = new Group(mapmult, Group.OperationTypes.Sort, getDataType(), getValueType());
				Aggregate agg1 = new Aggregate(grp, HopsAgg2Lops.get(outerOp), getDataType(), getValueType(), ExecType.MR);
				
				grp.getOutputParameters().setDimensions(getDim1(), getDim2(), getRowsInBlock(), getColsInBlock(), getNnz());
				agg1.getOutputParameters().setDimensions(getDim1(), getDim2(), getRowsInBlock(), getColsInBlock(), getNnz());
				setLineNumbers(agg1);
				
				// aggregation uses kahanSum but the inputs do not have correction values
				agg1.setupCorrectionLocation(CorrectionLocationType.NONE);  
				
				setLops(agg1);
			}
			else {
				setLops(mapmult);
			}
		}	
	} 

	private Lop constructMRLopsMapMMWithLeftTransposeRewrite() 
		throws HopsException, LopsException
	{
		Hop X = getInput().get(0).getInput().get(0); //guaranteed to exists
		Hop Y = getInput().get(1);
		
		//right vector transpose CP
		Lop tY = new Transform(Y.constructLops(), OperationTypes.Transpose, getDataType(), getValueType(), ExecType.CP);
		tY.getOutputParameters().setDimensions(Y.getDim2(), Y.getDim1(), getRowsInBlock(), getColsInBlock(), Y.getNnz());
		setLineNumbers(tY);
		
		//matrix mult
		
		// If number of columns is smaller than block size then explicit aggregation is not required.
		// i.e., entire matrix multiplication can be performed in the mappers.
		boolean needAgg = ( X.getDim1() <= 0 || X.getDim1() > X.getRowsInBlock() ); 
		boolean needPart = requiresPartitioning(MMultMethod.MAPMM_R, true); //R disregarding transpose rewrite
		
		//pre partitioning
		Lop dcinput = null;
		if( needPart ) {
			ExecType etPart = (OptimizerUtils.estimateSizeExactSparsity(Y.getDim2(), Y.getDim1(), OptimizerUtils.getSparsity(Y.getDim2(), Y.getDim1(), Y.getNnz())) 
					          < OptimizerUtils.getLocalMemBudget()) ? ExecType.CP : ExecType.MR; //operator selection
			dcinput = new DataPartition(tY, DataType.MATRIX, ValueType.DOUBLE, etPart, PDataPartitionFormat.COLUMN_BLOCK_WISE_N);
			dcinput.getOutputParameters().setDimensions(Y.getDim2(), Y.getDim1(), getRowsInBlock(), getColsInBlock(), Y.getNnz());
			setLineNumbers(dcinput);
		}
		else
			dcinput = tY;
		
		MapMult mapmult = new MapMult(dcinput, X.constructLops(), getDataType(), getValueType(), false, needPart, false);
		mapmult.getOutputParameters().setDimensions(Y.getDim2(), X.getDim2(), getRowsInBlock(), getColsInBlock(), getNnz());
		setLineNumbers(mapmult);
		
		//post aggregation 
		Lop mult = null;
		if( needAgg ) {
			Group grp = new Group(mapmult, Group.OperationTypes.Sort, getDataType(), getValueType());
			grp.getOutputParameters().setDimensions(Y.getDim2(), X.getDim2(), getRowsInBlock(), getColsInBlock(), getNnz());
			setLineNumbers(grp);
			
			Aggregate agg1 = new Aggregate(grp, HopsAgg2Lops.get(outerOp), getDataType(), getValueType(), ExecType.MR);
			agg1.getOutputParameters().setDimensions(Y.getDim2(), X.getDim2(), getRowsInBlock(), getColsInBlock(), getNnz());
			setLineNumbers(agg1);
			agg1.setupCorrectionLocation(CorrectionLocationType.NONE);  
			mult = agg1;
		}
		else
			mult = mapmult;
		
		//result transpose CP 
		Lop out = new Transform(mult, OperationTypes.Transpose, getDataType(), getValueType(), ExecType.CP);
		out.getOutputParameters().setDimensions(X.getDim2(), Y.getDim2(), getRowsInBlock(), getColsInBlock(), getNnz());
		
		return out;
	}

	private void constructMRLopsMapMMChain( ChainType chainType ) 
		throws HopsException, LopsException
	{
		Lop mapmult = null; 
		
		if( chainType == ChainType.XtXv )
		{
			//v never needs partitioning because always single block
			Hop hX = getInput().get(0).getInput().get(0);
			Hop hv = getInput().get(1).getInput().get(1);
			
			//core matrix mult
			mapmult = new MapMultChain( hX.constructLops(), hv.constructLops(), getDataType(), getValueType(), ExecType.MR);
			mapmult.getOutputParameters().setDimensions(getDim1(), getDim2(), getRowsInBlock(), getColsInBlock(), getNnz());
			setLineNumbers(mapmult);
		}
		else //ChainType.XtwXv / ChainType.XtXvy
		{
			//v never needs partitioning because always single block
			int wix = (chainType == ChainType.XtwXv) ? 0 : 1;
			int vix = (chainType == ChainType.XtwXv) ? 1 : 0;
			Hop hX = getInput().get(0).getInput().get(0);
			Hop hw = getInput().get(1).getInput().get(wix);
			Hop hv = getInput().get(1).getInput().get(vix).getInput().get(1);
			
			double mestW = OptimizerUtils.estimateSize(hw.getDim1(), hw.getDim2());
			boolean needPart = !hw.dimsKnown() || hw.getDim1() * hw.getDim2() > DistributedCacheInput.PARTITION_SIZE;
			Lop X = hX.constructLops(), v = hv.constructLops(), w = null;
			if( needPart ){ //requires partitioning
				w = new DataPartition(hw.constructLops(), DataType.MATRIX, ValueType.DOUBLE, (mestW>OptimizerUtils.getLocalMemBudget())?ExecType.MR:ExecType.CP, PDataPartitionFormat.ROW_BLOCK_WISE_N);
				w.getOutputParameters().setDimensions(hw.getDim1(), hw.getDim2(), getRowsInBlock(), getColsInBlock(), hw.getNnz());
				setLineNumbers(w);	
			}
			else
				w = hw.constructLops();
			
			//core matrix mult
			mapmult = new MapMultChain( X, v, w, chainType, getDataType(), getValueType(), ExecType.MR);
			mapmult.getOutputParameters().setDimensions(getDim1(), getDim2(), getRowsInBlock(), getColsInBlock(), getNnz());
			setLineNumbers(mapmult);
		}
		
		//post aggregation
		Group grp = new Group(mapmult, Group.OperationTypes.Sort, getDataType(), getValueType());
		grp.getOutputParameters().setDimensions(getDim1(), getDim2(), getRowsInBlock(), getColsInBlock(), getNnz());
		Aggregate agg1 = new Aggregate(grp, HopsAgg2Lops.get(outerOp), getDataType(), getValueType(), ExecType.MR);
		agg1.getOutputParameters().setDimensions(getDim1(), getDim2(), getRowsInBlock(), getColsInBlock(), getNnz());
		agg1.setupCorrectionLocation(CorrectionLocationType.NONE); // aggregation uses kahanSum 
		setLineNumbers(agg1);
		 
		setLops(agg1);
	} 

	private void constructMRLopsCPMM() 
		throws HopsException, LopsException
	{
		if( isLeftTransposeRewriteApplicable(false, false) )
		{
			setLops( constructMRLopsCPMMWithLeftTransposeRewrite() );
		} 
		else //general case
		{
			Hop X = getInput().get(0);
			Hop Y = getInput().get(1);
			
			MMCJType type = getMMCJAggregationType(X, Y);
			MMCJ mmcj = new MMCJ(X.constructLops(), Y.constructLops(), getDataType(), getValueType(), type, ExecType.MR);
			setOutputDimensions(mmcj);
			setLineNumbers(mmcj);
			
			Group grp = new Group(mmcj, Group.OperationTypes.Sort, getDataType(), getValueType());
			setOutputDimensions(grp);
			setLineNumbers(grp);
			
			Aggregate agg1 = new Aggregate(grp, HopsAgg2Lops.get(outerOp), getDataType(), getValueType(), ExecType.MR);
			setOutputDimensions(agg1);
			setLineNumbers(agg1);
			
			// aggregation uses kahanSum but the inputs do not have correction values
			agg1.setupCorrectionLocation(CorrectionLocationType.NONE);  
			
			setLops(agg1);
		}
	} 

	private Lop constructMRLopsCPMMWithLeftTransposeRewrite() 
		throws HopsException, LopsException
	{
		Hop X = getInput().get(0).getInput().get(0); //guaranteed to exists
		Hop Y = getInput().get(1);
		
		//right vector transpose CP
		Lop tY = new Transform(Y.constructLops(), OperationTypes.Transpose, getDataType(), getValueType(), ExecType.CP);
		tY.getOutputParameters().setDimensions(Y.getDim2(), Y.getDim1(), getRowsInBlock(), getColsInBlock(), Y.getNnz());
		setLineNumbers(tY);
		
		//matrix multiply
		MMCJType type = getMMCJAggregationType(X, Y);
		MMCJ mmcj = new MMCJ(tY, X.constructLops(), getDataType(), getValueType(), type, ExecType.MR);
		setOutputDimensions(mmcj);
		setLineNumbers(mmcj);
		
		Group grp = new Group(mmcj, Group.OperationTypes.Sort, getDataType(), getValueType());
		setOutputDimensions(grp);
		setLineNumbers(grp);
		
		Aggregate agg1 = new Aggregate(grp, HopsAgg2Lops.get(outerOp), getDataType(), getValueType(), ExecType.MR);
		setOutputDimensions(agg1);
		setLineNumbers(agg1);
		
		// aggregation uses kahanSum but the inputs do not have correction values
		agg1.setupCorrectionLocation(CorrectionLocationType.NONE);  

		
		//result transpose CP 
		Lop out = new Transform(agg1, OperationTypes.Transpose, getDataType(), getValueType(), ExecType.CP);
		out.getOutputParameters().setDimensions(X.getDim2(), Y.getDim2(), getRowsInBlock(), getColsInBlock(), getNnz());
		
		return out;
	}

	private void constructMRLopsRMM() 
		throws HopsException, LopsException
	{
		MMRJ rmm = new MMRJ(getInput().get(0).constructLops(), getInput().get(1).constructLops(), 
				            getDataType(), getValueType(), ExecType.MR);
		
		setOutputDimensions(rmm);
		setLineNumbers(rmm);
		setLops(rmm);
	} 

	private void constructMRLopsTSMM(MMTSJType mmtsj) 
		throws HopsException, LopsException
	{
		Hop input = getInput().get(mmtsj.isLeft()?1:0);
		
		MMTSJ tsmm = new MMTSJ(input.constructLops(), getDataType(), getValueType(), ExecType.MR, mmtsj);
		tsmm.getOutputParameters().setDimensions(getDim1(), getDim2(), getRowsInBlock(), getColsInBlock(), getNnz());
		setLineNumbers(tsmm);
		
		Aggregate agg1 = new Aggregate(tsmm, HopsAgg2Lops.get(outerOp), getDataType(), getValueType(), ExecType.MR);
		agg1.getOutputParameters().setDimensions(getDim1(), getDim2(), getRowsInBlock(), getColsInBlock(), getNnz());
		agg1.setupCorrectionLocation(CorrectionLocationType.NONE); // aggregation uses kahanSum but the inputs do not have correction values
		setLineNumbers(agg1);
		
		setLops(agg1);
	} 

	private void constructMRLopsPMM() 
		throws HopsException, LopsException
	{
		//PMM has two potential modes (a) w/ full permutation matrix input, and 
		//(b) w/ already condensed input vector of target row positions.
		
		Hop pmInput = getInput().get(0);
		Hop rightInput = getInput().get(1);
		
		Lop lpmInput = pmInput.constructLops();
		Hop nrow = null;
		double mestPM = OptimizerUtils.estimateSize(pmInput.getDim1(), 1);
		ExecType etVect = (mestPM>OptimizerUtils.getLocalMemBudget())?ExecType.MR:ExecType.CP;
		
		//a) full permutation matrix input (potentially without empty block materialized)
		if( pmInput.getDim2() != 1 ) //not a vector
		{
			//compute condensed permutation matrix vector input			
			//v = rowMaxIndex(t(pm)) * rowMax(t(pm)) 
			ReorgOp transpose = HopRewriteUtils.createTranspose(pmInput);
			transpose.setForcedExecType(ExecType.MR);
			
			AggUnaryOp agg1 = HopRewriteUtils.createAggUnaryOp(transpose, AggOp.MAXINDEX, Direction.Row);
			agg1.setForcedExecType(ExecType.MR);
			
			AggUnaryOp agg2 = HopRewriteUtils.createAggUnaryOp(transpose, AggOp.MAX, Direction.Row);
			agg2.setForcedExecType(ExecType.MR);
			
			BinaryOp mult = HopRewriteUtils.createBinary(agg1, agg2, OpOp2.MULT);
			mult.setForcedExecType(ExecType.MR);
			
			//compute NROW target via nrow(m)
			nrow = HopRewriteUtils.createValueHop(pmInput, true);
			nrow.setOutputBlocksizes(0, 0);
			nrow.setForcedExecType(ExecType.CP);
			HopRewriteUtils.copyLineNumbers(this, nrow);
				
			lpmInput = mult.constructLops();			
			HopRewriteUtils.removeChildReference(pmInput, transpose);
		}
		else //input vector
		{
			//compute NROW target via max(v)
			nrow = HopRewriteUtils.createAggUnaryOp(pmInput, AggOp.MAX, Direction.RowCol); 
			nrow.setOutputBlocksizes(0, 0);
			nrow.setForcedExecType(etVect);
			HopRewriteUtils.copyLineNumbers(this, nrow);
		}
		
		//b) condensed permutation matrix vector input (target rows)		
		boolean needPart = !pmInput.dimsKnown() || pmInput.getDim1() > DistributedCacheInput.PARTITION_SIZE;
		if( needPart ){ //requires partitioning
			lpmInput = new DataPartition(lpmInput, DataType.MATRIX, ValueType.DOUBLE, etVect, PDataPartitionFormat.ROW_BLOCK_WISE_N);
			lpmInput.getOutputParameters().setDimensions(pmInput.getDim1(), 1, getRowsInBlock(), getColsInBlock(), pmInput.getDim1());
			setLineNumbers(lpmInput);	
		}
		
		_outputEmptyBlocks = !OptimizerUtils.allowsToFilterEmptyBlockOutputs(this); 
		PMMJ pmm = new PMMJ(lpmInput, rightInput.constructLops(), nrow.constructLops(), getDataType(), getValueType(), needPart, _outputEmptyBlocks, ExecType.MR);
		pmm.getOutputParameters().setDimensions(getDim1(), getDim2(), getRowsInBlock(), getColsInBlock(), getNnz());
		setLineNumbers(pmm);
		
		Aggregate aggregate = new Aggregate(pmm, HopsAgg2Lops.get(outerOp), getDataType(), getValueType(), ExecType.MR);
		aggregate.getOutputParameters().setDimensions(getDim1(), getDim2(), getRowsInBlock(), getColsInBlock(), getNnz());
		aggregate.setupCorrectionLocation(CorrectionLocationType.NONE); // aggregation uses kahanSum but the inputs do not have correction values
		setLineNumbers(aggregate);
		setLops(aggregate);
		
		HopRewriteUtils.removeChildReference(pmInput, nrow);		
	} 
	
	
	
	/**
	 * Determines if the rewrite t(X)%*%Y -> t(t(Y)%*%X) is applicable
	 * and cost effective. Whenever X is a wide matrix and Y is a vector
	 * this has huge impact, because the transpose of X would dominate
	 * the entire operation costs.
	 * 
	 * @param CP true if CP
	 * @param checkMemMR true if check MR memory
	 * @return true if left transpose rewrite applicable
	 */
	private boolean isLeftTransposeRewriteApplicable(boolean CP, boolean checkMemMR)
	{
		//check for forced MR or Spark execution modes, which prevent the introduction of
		//additional CP operations and hence the rewrite application
		if(    DMLScript.rtplatform == RUNTIME_PLATFORM.HADOOP  //not hybrid_mr
			|| DMLScript.rtplatform == RUNTIME_PLATFORM.SPARK ) //not hybrid_spark
		{
			return false;
		}
		
		boolean ret = false;
		Hop h1 = getInput().get(0);
		Hop h2 = getInput().get(1);
		
		//check for known dimensions and cost for t(X) vs t(v) + t(tvX)
		//(for both CP/MR, we explicitly check that new transposes fit in memory,
		//even a ba in CP does not imply that both transposes can be executed in CP)
		if( CP ) //in-memory ba 
		{
			if( HopRewriteUtils.isTransposeOperation(h1) )
			{
				long m = h1.getDim1();
				long cd = h1.getDim2();
				long n = h2.getDim2();
				
				//check for known dimensions (necessary condition for subsequent checks)
				ret = (m>0 && cd>0 && n>0); 
				
				//check operation memory with changed transpose (this is important if we have 
				//e.g., t(X) %*% v, where X is sparse and tX fits in memory but X does not
				double memX = h1.getInput().get(0).getOutputMemEstimate();
				double memtv = OptimizerUtils.estimateSizeExactSparsity(n, cd, 1.0);
				double memtXv = OptimizerUtils.estimateSizeExactSparsity(n, m, 1.0);
				double newMemEstimate = memtv + memX + memtXv;
				ret &= ( newMemEstimate < OptimizerUtils.getLocalMemBudget() );
				
				//check for cost benefit of t(X) vs t(v) + t(tvX) and memory of additional transpose ops
				ret &= ( m*cd > (cd*n + m*n) &&
					2 * OptimizerUtils.estimateSizeExactSparsity(cd, n, 1.0) < OptimizerUtils.getLocalMemBudget() &&
					2 * OptimizerUtils.estimateSizeExactSparsity(m, n, 1.0) < OptimizerUtils.getLocalMemBudget() ); 
				
				//update operation memory estimate (e.g., for parfor optimizer)
				if( ret )
					_memEstimate = newMemEstimate;
			}
		}
		else //MR
		{
			if( h1 instanceof ReorgOp && ((ReorgOp)h1).getOp()==ReOrgOp.TRANSPOSE )
			{
				long m = h1.getDim1();
				long cd = h1.getDim2();
				long n = h2.getDim2();
				
				
				//note: output size constraint for mapmult already checked by optfindmmultmethod
				if( m>0 && cd>0 && n>0 && (m*cd > (cd*n + m*n)) &&
					2 * OptimizerUtils.estimateSizeExactSparsity(cd, n, 1.0) <  OptimizerUtils.getLocalMemBudget() &&
					2 * OptimizerUtils.estimateSizeExactSparsity(m, n, 1.0) <  OptimizerUtils.getLocalMemBudget() &&
					(!checkMemMR || OptimizerUtils.estimateSizeExactSparsity(cd, n, 1.0) < OptimizerUtils.getRemoteMemBudgetMap(true)) ) 
				{
					ret = true;
				}
			}
		}
		
		return ret;
	}

	private MMCJType getMMCJAggregationType(Hop X, Hop Y)
	{
		//choose quickpath (no aggregation) if the aggregation buffer likely has to spill and the smaller block fits
		//into the minimal cache size and hence is guaranteed not to require spilling
		double sizeX = OptimizerUtils.estimateSize(X.getDim1(), Math.min(X.getDim2(), X.getColsInBlock()));
		double sizeY = OptimizerUtils.estimateSize(Math.min(Y.getDim1(), Y.getRowsInBlock()), Y.getDim2());
		
		return (dimsKnown() && 2*OptimizerUtils.estimateSize(getDim1(), getDim2())>OptimizerUtils.getRemoteMemBudgetReduce()
			&& (  sizeX < MMCJMRReducerWithAggregator.MIN_CACHE_SIZE 
			   || sizeY < MMCJMRReducerWithAggregator.MIN_CACHE_SIZE) ) 
			   ? MMCJType.NO_AGG : MMCJType.AGG ;
	}

	private SparkAggType getSparkMMAggregationType( boolean agg )
	{
		if( !agg )
			return SparkAggType.NONE;
		
		if( dimsKnown() && getDim1()<=getRowsInBlock() && getDim2()<=getColsInBlock() )
			return SparkAggType.SINGLE_BLOCK;
		else
			return SparkAggType.MULTI_BLOCK;
	}

	private boolean requiresAggregation(MMultMethod method) 
	{
		//worst-case assumption (for plan correctness)
		boolean ret = true;
		
		//right side cached (no agg if left has just one column block)
		if(  method == MMultMethod.MAPMM_R && getInput().get(0).getDim2() > 0 //known num columns
	         && getInput().get(0).getDim2() <= getInput().get(0).getColsInBlock() ) 
        {
            ret = false;
        }
        
		//left side cached (no agg if right has just one row block)
        if(  method == MMultMethod.MAPMM_L && getInput().get(1).getDim1() > 0 //known num rows
             && getInput().get(1).getDim1() <= getInput().get(1).getRowsInBlock() ) 
        {
       	    ret = false;
        }
        
        return ret;
	}

	private boolean requiresPartitioning(MMultMethod method, boolean rewrite) 
	{
		boolean ret = true; //worst-case
		Hop input1 = getInput().get(0);
		Hop input2 = getInput().get(1);
		
		//right side cached 
		if(  method == MMultMethod.MAPMM_R && input2.dimsKnown() ) { //known input size 
            ret = (input2.getDim1()*input2.getDim2() > DistributedCacheInput.PARTITION_SIZE);
            
            //conservative: do not apply partitioning if this forces t(X) into separate job
            //if( !rewrite && input1 instanceof ReorgOp && ((ReorgOp)input1).getOp()==ReOrgOp.TRANSPOSE )
            //	ret = false;
        }
        
		//left side cached (no agg if right has just one row block)
		if(  method == MMultMethod.MAPMM_L && input1.dimsKnown() ) { //known input size 
            ret = (input1.getDim1()*input1.getDim2() > DistributedCacheInput.PARTITION_SIZE);
            
            //conservative: do not apply partitioning if this forces t(X) into separate job
            //if( !rewrite && input2 instanceof ReorgOp && ((ReorgOp)input2).getOp()==ReOrgOp.TRANSPOSE )
            //	ret = false;
        }
        
		return ret;
	}
	
	/**
	 * Estimates the memory footprint of MapMult operation depending on which input is put into distributed cache.
	 * This function is called by <code>optFindMMultMethod()</code> to decide the execution strategy, as well as by 
	 * piggybacking to decide the number of Map-side instructions to put into a single GMR job.
	 * 
	 * @param m1_rows m1 rows
	 * @param m1_cols m1 cols
	 * @param m1_rpb m1 rows per block
	 * @param m1_cpb m1 cols per block
	 * @param m1_nnz m1 num non-zeros
	 * @param m2_rows m2 rows
	 * @param m2_cols m2 cols
	 * @param m2_rpb m2 rows per block
	 * @param m2_cpb m2 cols per block
	 * @param m2_nnz m2 num non-zeros
	 * @param cachedInputIndex true if cached input index
	 * @param pmm true if permutation matrix multiply
	 * @return map mm memory estimate
	 */
	public static double getMapmmMemEstimate(long m1_rows, long m1_cols, long m1_rpb, long m1_cpb, long m1_nnz,
			long m2_rows, long m2_cols, long m2_rpb, long m2_cpb, long m2_nnz, int cachedInputIndex, boolean pmm) 
	{
		// If the size of one input is small, choose a method that uses distributed cache
		// NOTE: be aware of output size because one input block might generate many output blocks
		double m1SizeP = OptimizerUtils.estimatePartitionedSizeExactSparsity(m1_rows, m1_cols, m1_rpb, m1_cpb, m1_nnz); //m1 partitioned 
		double m2SizeP = OptimizerUtils.estimatePartitionedSizeExactSparsity(m2_rows, m2_cols, m2_rpb, m2_cpb, m2_nnz); //m2 partitioned
		
		double m1BlockSize = OptimizerUtils.estimateSize(Math.min(m1_rows, m1_rpb), Math.min(m1_cols, m1_cpb));
		double m2BlockSize = OptimizerUtils.estimateSize(Math.min(m2_rows, m2_rpb), Math.min(m2_cols, m2_cpb));
		double m3m1OutSize = OptimizerUtils.estimateSize(Math.min(m1_rows, m1_rpb), m2_cols); //output per m1 block if m2 in cache
		double m3m2OutSize = OptimizerUtils.estimateSize(m1_rows, Math.min(m2_cols, m2_cpb)); //output per m2 block if m1 in cache
	
		double footprint = 0;
		if( pmm )
		{
			//permutation matrix multiply 
			//(one input block -> at most two output blocks)
			footprint = m1SizeP + 3*m2BlockSize; //in+2*out
		}
		else
		{
			//generic matrix multiply
			if ( cachedInputIndex == 1 ) {
				// left input (m1) is in cache
				footprint = m1SizeP+m2BlockSize+m3m2OutSize;
			}
			else {
				// right input (m2) is in cache
				footprint = m1BlockSize+m2SizeP+m3m1OutSize;
			}	
		}
		
		return footprint;
	}
	
	/**
	 * Optimization that chooses between two methods to perform matrix multiplication on map-reduce.
	 * 
	 * More details on the cost-model used: refer ICDE 2011 paper.
	 * 
	 * @param m1_rows m1 rows
	 * @param m1_cols m1 cols
	 * @param m1_rpb m1 rows per block
	 * @param m1_cpb m1 cols per block
	 * @param m1_nnz m1 num non-zeros
	 * @param m2_rows m2 rows
	 * @param m2_cols m2 cols
	 * @param m2_rpb m2 rows per block
	 * @param m2_cpb m2 cols per block
	 * @param m2_nnz m2 num non-zeros
	 * @param mmtsj the MMTSJType
	 * @param chainType the chain type
	 * @param leftPMInput the left pm input
	 * @return the MMultMethod
	 */
	private static MMultMethod optFindMMultMethodMR ( long m1_rows, long m1_cols, long m1_rpb, long m1_cpb, long m1_nnz,
			                                        long m2_rows, long m2_cols, long m2_rpb, long m2_cpb, long m2_nnz,
			                                        MMTSJType mmtsj, ChainType chainType, boolean leftPMInput ) 
	{	
		double memBudget = MAPMULT_MEM_MULTIPLIER * OptimizerUtils.getRemoteMemBudgetMap(true);		
		
		// Step 0: check for forced mmultmethod
		if( FORCED_MMULT_METHOD !=null )
			return FORCED_MMULT_METHOD;
		
		// Step 1: check TSMM
		// If transpose self pattern and result is single block:
		// use specialized TSMM method (always better than generic jobs)
		if(    ( mmtsj == MMTSJType.LEFT && m2_cols>=0 && m2_cols <= m2_cpb )
			|| ( mmtsj == MMTSJType.RIGHT && m1_rows>=0 && m1_rows <= m1_rpb ) )
		{
			return MMultMethod.TSMM;
		}

		// Step 2: check MapMultChain
		// If mapmultchain pattern and result is a single block:
		// use specialized mapmult method
		if( OptimizerUtils.ALLOW_SUM_PRODUCT_REWRITES )
		{
			//matmultchain if dim2(X)<=blocksize and all vectors fit in mappers
			//(X: m1_cols x m1_rows, v: m1_rows x m2_cols, w: m1_cols x m2_cols) 
			//NOTE: generalization possibe: m2_cols>=0 && m2_cols<=m2_cpb
			if( chainType!=ChainType.NONE && m1_rows>=0 && m1_rows<= m1_rpb  && m2_cols==1 )
			{
				if( chainType==ChainType.XtXv && m1_rows>=0 && m2_cols>=0 
					&& OptimizerUtils.estimateSize(m1_rows, m2_cols ) < memBudget )
				{
					return MMultMethod.MAPMM_CHAIN;
				}
				else if( (chainType==ChainType.XtwXv || chainType==ChainType.XtXvy )
					&& m1_rows>=0 && m2_cols>=0 && m1_cols>=0
					&&   OptimizerUtils.estimateSize(m1_rows, m2_cols ) 
					   + OptimizerUtils.estimateSize(m1_cols, m2_cols) < memBudget )
				{
					return MMultMethod.MAPMM_CHAIN;
				}
			}
		}
		
		// Step 3: check for PMM (permutation matrix needs to fit into mapper memory)
		// (needs to be checked before mapmult for consistency with removeEmpty compilation 
		double footprintPM1 = getMapmmMemEstimate(m1_rows, 1, m1_rpb, m1_cpb, m1_nnz, m2_rows, m2_cols, m2_rpb, m2_cpb, m2_nnz, 1, true);
		double footprintPM2 = getMapmmMemEstimate(m2_rows, 1, m1_rpb, m1_cpb, m1_nnz, m2_rows, m2_cols, m2_rpb, m2_cpb, m2_nnz, 1, true);
		if( (footprintPM1 < memBudget && m1_rows>=0 || footprintPM2 < memBudget && m2_rows>=0 ) 
			&& leftPMInput ) 
		{
			return MMultMethod.PMM;
		}
		
		// Step 4: check MapMult
		// If the size of one input is small, choose a method that uses distributed cache
		// (with awareness of output size because one input block might generate many output blocks)		
		//memory estimates for local partitioning (mb -> partitioned mb)
		double m1SizeP = OptimizerUtils.estimatePartitionedSizeExactSparsity(m1_rows, m1_cols, m1_rpb, m1_cpb, m1_nnz); //m1 partitioned 
		double m2SizeP = OptimizerUtils.estimatePartitionedSizeExactSparsity(m2_rows, m2_cols, m2_rpb, m2_cpb, m2_nnz); //m2 partitioned
		
		//memory estimates for remote execution (broadcast and outputs)
		double footprint1 = getMapmmMemEstimate(m1_rows, m1_cols, m1_rpb, m1_cpb, m1_nnz, m2_rows, m2_cols, m2_rpb, m2_cpb, m2_nnz, 1, false);
		double footprint2 = getMapmmMemEstimate(m1_rows, m1_cols, m1_rpb, m1_cpb, m1_nnz, m2_rows, m2_cols, m2_rpb, m2_cpb, m2_nnz, 2, false);		
		
		if (   (footprint1 < memBudget && m1_rows>=0 && m1_cols>=0)
			|| (footprint2 < memBudget && m2_rows>=0 && m2_cols>=0) ) 
		{
			//apply map mult if one side fits in remote task memory 
			//(if so pick smaller input for distributed cache)
			if( m1SizeP < m2SizeP && m1_rows>=0 && m1_cols>=0)
				return MMultMethod.MAPMM_L;
			else
				return MMultMethod.MAPMM_R;
		}
		
		// Step 5: check for unknowns
		// If the dimensions are unknown at compilation time, simply assume 
		// the worst-case scenario and produce the most robust plan -- which is CPMM
		if ( m1_rows == -1 || m1_cols == -1 || m2_rows == -1 || m2_cols == -1 )
			return MMultMethod.CPMM;

		// Step 6: Decide CPMM vs RMM based on io costs

		//estimate shuffle costs weighted by parallelism
		double rmm_costs = getRMMCostEstimate(m1_rows, m1_cols, m1_rpb, m1_cpb, m2_rows, m2_cols, m2_rpb, m2_cpb);
		double cpmm_costs = getCPMMCostEstimate(m1_rows, m1_cols, m1_rpb, m1_cpb, m2_rows, m2_cols, m2_rpb, m2_cpb);
				
		//final mmult method decision 
		if ( cpmm_costs < rmm_costs ) 
			return MMultMethod.CPMM;
		else 
			return MMultMethod.RMM;
	}

	private static MMultMethod optFindMMultMethodCP( long m1_rows, long m1_cols, long m2_rows, long m2_cols, MMTSJType mmtsj, ChainType chainType, boolean leftPM ) 
	{	
		//step 1: check for TSMM pattern
		if( mmtsj != MMTSJType.NONE )
			return MMultMethod.TSMM;
		
		//step 2: check for MMChain pattern
		if( chainType != ChainType.NONE && OptimizerUtils.ALLOW_SUM_PRODUCT_REWRITES && m2_cols==1 )
			return MMultMethod.MAPMM_CHAIN;
		
		//step 3: check for PMM
		if( leftPM && m1_cols==1 && m2_rows!=1 )
			return MMultMethod.PMM;
		
		//step 4: general purpose MM
		return MMultMethod.MM; 
	}
	
	private MMultMethod optFindMMultMethodSpark( long m1_rows, long m1_cols, long m1_rpb, long m1_cpb, long m1_nnz, 
            long m2_rows, long m2_cols, long m2_rpb, long m2_cpb, long m2_nnz,
            MMTSJType mmtsj, ChainType chainType, boolean leftPMInput, boolean tmmRewrite ) 
	{	
		//Notes: Any broadcast needs to fit twice in local memory because we partition the input in cp,
		//and needs to fit once in executor broadcast memory. The 2GB broadcast constraint is no longer
		//required because the max_int byte buffer constraint has been fixed in Spark 1.4 
		double memBudgetExec = MAPMULT_MEM_MULTIPLIER * SparkExecutionContext.getBroadcastMemoryBudget();		
		double memBudgetLocal = OptimizerUtils.getLocalMemBudget();

		//reset spark broadcast memory information (for concurrent parfor jobs, awareness of additional 
		//cp memory requirements on spark rdd operations with broadcasts)
		_spBroadcastMemEstimate = 0;
		
		// Step 0: check for forced mmultmethod
		if( FORCED_MMULT_METHOD !=null )
			return FORCED_MMULT_METHOD;
		
		// Step 1: check TSMM
		// If transpose self pattern and result is single block:
		// use specialized TSMM method (always better than generic jobs)
		if(    ( mmtsj == MMTSJType.LEFT && m2_cols>=0 && m2_cols <= m2_cpb )
			|| ( mmtsj == MMTSJType.RIGHT && m1_rows>=0 && m1_rows <= m1_rpb ) )
		{
			return MMultMethod.TSMM;
		}
		
		// Step 2: check MapMMChain
		// If mapmultchain pattern and result is a single block:
		// use specialized mapmult method
		if( OptimizerUtils.ALLOW_SUM_PRODUCT_REWRITES )
		{
			//matmultchain if dim2(X)<=blocksize and all vectors fit in mappers
			//(X: m1_cols x m1_rows, v: m1_rows x m2_cols, w: m1_cols x m2_cols) 
			//NOTE: generalization possibe: m2_cols>=0 && m2_cols<=m2_cpb
			if( chainType!=ChainType.NONE && m1_rows >=0 && m1_rows <= m1_rpb && m2_cols==1 )
			{
				if( chainType==ChainType.XtXv && m1_rows>=0 && m2_cols>=0 
					&& OptimizerUtils.estimateSize(m1_rows, m2_cols ) < memBudgetExec )
				{
					return MMultMethod.MAPMM_CHAIN;
				}
				else if( (chainType==ChainType.XtwXv || chainType==ChainType.XtXvy ) 
					&& m1_rows>=0 && m2_cols>=0 && m1_cols>=0
					&&   OptimizerUtils.estimateSize(m1_rows, m2_cols) 
					   + OptimizerUtils.estimateSize(m1_cols, m2_cols) < memBudgetExec
					&& 2*(OptimizerUtils.estimateSize(m1_rows, m2_cols) 
					   + OptimizerUtils.estimateSize(m1_cols, m2_cols)) < memBudgetLocal )
				{
					_spBroadcastMemEstimate = 2*(OptimizerUtils.estimateSize(m1_rows, m2_cols) 
							   				   + OptimizerUtils.estimateSize(m1_cols, m2_cols));
					return MMultMethod.MAPMM_CHAIN;
				}
			}
		}		
		
		// Step 3: check for PMM (permutation matrix needs to fit into mapper memory)
		// (needs to be checked before mapmult for consistency with removeEmpty compilation 
		double footprintPM1 = getMapmmMemEstimate(m1_rows, 1, m1_rpb, m1_cpb, m1_nnz, m2_rows, m2_cols, m2_rpb, m2_cpb, m2_nnz, 1, true);
		double footprintPM2 = getMapmmMemEstimate(m2_rows, 1, m1_rpb, m1_cpb, m1_nnz, m2_rows, m2_cols, m2_rpb, m2_cpb, m2_nnz, 1, true);
		if( (footprintPM1 < memBudgetExec && m1_rows>=0 || footprintPM2 < memBudgetExec && m2_rows>=0)
			&& 2*OptimizerUtils.estimateSize(m1_rows, 1) < memBudgetLocal
			&& leftPMInput ) 
		{
			_spBroadcastMemEstimate = 2*OptimizerUtils.estimateSize(m1_rows, 1);
			return MMultMethod.PMM;
		}
		
		// Step 4: check MapMM
		// If the size of one input is small, choose a method that uses broadcast variables to prevent shuffle
		
		//memory estimates for local partitioning (mb -> partitioned mb)
		double m1Size = OptimizerUtils.estimateSizeExactSparsity(m1_rows, m1_cols, m1_nnz); //m1 single block
		double m2Size = OptimizerUtils.estimateSizeExactSparsity(m2_rows, m2_cols, m2_nnz); //m2 single block
		double m1SizeP = OptimizerUtils.estimatePartitionedSizeExactSparsity(m1_rows, m1_cols, m1_rpb, m1_cpb, m1_nnz); //m1 partitioned 
		double m2SizeP = OptimizerUtils.estimatePartitionedSizeExactSparsity(m2_rows, m2_cols, m2_rpb, m2_cpb, m2_nnz); //m2 partitioned
		
		//memory estimates for remote execution (broadcast and outputs)
		double footprint1 = getMapmmMemEstimate(m1_rows, m1_cols, m1_rpb, m1_cpb, m1_nnz, m2_rows, m2_cols, m2_rpb, m2_cpb, m2_nnz, 1, false);
		double footprint2 = getMapmmMemEstimate(m1_rows, m1_cols, m1_rpb, m1_cpb, m1_nnz, m2_rows, m2_cols, m2_rpb, m2_cpb, m2_nnz, 2, false);		
		
		if (   (footprint1 < memBudgetExec && m1Size+m1SizeP < memBudgetLocal && m1_rows>=0 && m1_cols>=0)
			|| (footprint2 < memBudgetExec && m2Size+m2SizeP < memBudgetLocal && m2_rows>=0 && m2_cols>=0) ) 
		{
			//apply map mult if one side fits in remote task memory 
			//(if so pick smaller input for distributed cache)
			if( m1SizeP < m2SizeP && m1_rows>=0 && m1_cols>=0) {
				_spBroadcastMemEstimate = m1Size+m1SizeP;
				return MMultMethod.MAPMM_L;
			}
			else {
				_spBroadcastMemEstimate = m2Size+m2SizeP;
				return MMultMethod.MAPMM_R;
			}
		}
		
		// Step 5: check for TSMM2 (2 pass w/o suffle, preferred over CPMM/RMM)
		if( mmtsj != MMTSJType.NONE && m1_rows >=0 && m1_cols>=0 
			&& m2_rows >= 0 && m2_cols>=0 )
		{
			double mSize = (mmtsj == MMTSJType.LEFT) ? 
					OptimizerUtils.estimateSizeExactSparsity(m2_rows, m2_cols-m2_cpb, 1.0) : 
					OptimizerUtils.estimateSizeExactSparsity(m1_rows-m1_rpb, m1_cols, 1.0);	
			double mSizeP = (mmtsj == MMTSJType.LEFT) ? 
					OptimizerUtils.estimatePartitionedSizeExactSparsity(m2_rows, m2_cols-m2_cpb, m2_rpb, m2_cpb, 1.0) : 
					OptimizerUtils.estimatePartitionedSizeExactSparsity(m1_rows-m1_rpb, m1_cols, m1_rpb, m1_cpb, 1.0); 
			if( mSizeP < memBudgetExec && mSize+mSizeP < memBudgetLocal 
				&& ((mmtsj == MMTSJType.LEFT) ? m2_cols<=2*m2_cpb : m1_rows<=2*m1_rpb) //4 output blocks
				&& mSizeP < 2L*1024*1024*1024) { //2GB limitation as single broadcast
				return MMultMethod.TSMM2;
			}
		}
		
		// Step 6: check for unknowns
		// If the dimensions are unknown at compilation time, simply assume 
		// the worst-case scenario and produce the most robust plan -- which is CPMM
		if ( m1_rows == -1 || m1_cols == -1 || m2_rows == -1 || m2_cols == -1 )
			return MMultMethod.CPMM;

		// Step 7: check for ZIPMM
		// If t(X)%*%y -> t(t(y)%*%X) rewrite and ncol(X)<blocksize
		if( tmmRewrite && m1_rows >= 0 && m1_rows <= m1_rpb  //blocksize constraint left
			&& m2_cols >= 0 && m2_cols <= m2_cpb )           //blocksize constraint right	
		{
			return MMultMethod.ZIPMM;
		}
			
		// Step 8: Decide CPMM vs RMM based on io costs
		//estimate shuffle costs weighted by parallelism
		//TODO currently we reuse the mr estimates, these need to be fine-tune for our spark operators
		double rmm_costs = getRMMCostEstimate(m1_rows, m1_cols, m1_rpb, m1_cpb, m2_rows, m2_cols, m2_rpb, m2_cpb);
		double cpmm_costs = getCPMMCostEstimate(m1_rows, m1_cols, m1_rpb, m1_cpb, m2_rows, m2_cols, m2_rpb, m2_cpb);
				
		//final mmult method decision 
		if ( cpmm_costs < rmm_costs ) 
			return MMultMethod.CPMM;
		else 
			return MMultMethod.RMM;
	}

	private static double getRMMCostEstimate( long m1_rows, long m1_cols, long m1_rpb, long m1_cpb, 
			long m2_rows, long m2_cols, long m2_rpb, long m2_cpb )
	{
		long m1_nrb = (long) Math.ceil((double)m1_rows/m1_rpb); // number of row blocks in m1
		long m2_ncb = (long) Math.ceil((double)m2_cols/m2_cpb); // number of column blocks in m2

		// TODO: we must factor in the "sparsity"
		double m1_size = m1_rows * m1_cols;
		double m2_size = m2_rows * m2_cols;
		double result_size = m1_rows * m2_cols;

		int numReducersRMM = OptimizerUtils.getNumReducers(true);
		
		// Estimate the cost of RMM
		// RMM phase 1
		double rmm_shuffle = (m2_ncb*m1_size) + (m1_nrb*m2_size);
		double rmm_io = m1_size + m2_size + result_size;
		double rmm_nred = Math.min( m1_nrb * m2_ncb, //max used reducers 
				                    numReducersRMM); //available reducers
		// RMM total costs
		double rmm_costs = (rmm_shuffle + rmm_io) / rmm_nred;
		
		// return total costs
		return rmm_costs;
	}

	private static double getCPMMCostEstimate( long m1_rows, long m1_cols, long m1_rpb, long m1_cpb, 
            long m2_rows, long m2_cols, long m2_rpb, long m2_cpb )
	{
		long m1_nrb = (long) Math.ceil((double)m1_rows/m1_rpb); // number of row blocks in m1
		long m1_ncb = (long) Math.ceil((double)m1_cols/m1_cpb); // number of column blocks in m1
		long m2_ncb = (long) Math.ceil((double)m2_cols/m2_cpb); // number of column blocks in m2

		// TODO: we must factor in the "sparsity"
		double m1_size = m1_rows * m1_cols;
		double m2_size = m2_rows * m2_cols;
		double result_size = m1_rows * m2_cols;

		int numReducersCPMM = OptimizerUtils.getNumReducers(false);
		
		// Estimate the cost of CPMM
		// CPMM phase 1
		double cpmm_shuffle1 = m1_size + m2_size;
		double cpmm_nred1 = Math.min( m1_ncb, //max used reducers 
                                      numReducersCPMM); //available reducers		
		double cpmm_io1 = m1_size + m2_size + cpmm_nred1 * result_size;
		// CPMM phase 2
		double cpmm_shuffle2 = cpmm_nred1 * result_size;
		double cpmm_io2 = cpmm_nred1 * result_size + result_size;			
		double cpmm_nred2 = Math.min( m1_nrb * m2_ncb, //max used reducers 
                                      numReducersCPMM); //available reducers		
		// CPMM total costs
		double cpmm_costs =  (cpmm_shuffle1+cpmm_io1)/cpmm_nred1  //cpmm phase1
		                    +(cpmm_shuffle2+cpmm_io2)/cpmm_nred2; //cpmm phase2
		
		//return total costs
		return cpmm_costs;
	}
	
	@Override
	public void refreshSizeInformation()
	{
		Hop input1 = getInput().get(0);
		Hop input2 = getInput().get(1);
		
		if( isMatrixMultiply() ) {
			setDim1(input1.getDim1());
			setDim2(input2.getDim2());
		}
	}
	
	@Override
	public Object clone() throws CloneNotSupportedException 
	{
		AggBinaryOp ret = new AggBinaryOp(innerOp, outerOp);
		
		//copy generic attributes
		ret.clone(this, false);
		
		//copy specific attributes
		ret._hasLeftPMInput = _hasLeftPMInput;
		ret._maxNumThreads = _maxNumThreads;
		
		return ret;
	}
	
	@Override
	public boolean compare( Hop that )
	{
		if( !(that instanceof AggBinaryOp) )
			return false;
		
		AggBinaryOp that2 = (AggBinaryOp)that;
		return (   innerOp == that2.innerOp
				&& outerOp == that2.outerOp
				&& getInput().get(0) == that2.getInput().get(0)
				&& getInput().get(1) == that2.getInput().get(1)
				&& _hasLeftPMInput == that2._hasLeftPMInput
				&& _maxNumThreads == that2._maxNumThreads);
	}
}

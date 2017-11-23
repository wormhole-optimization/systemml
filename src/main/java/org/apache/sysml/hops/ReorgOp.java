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

import java.util.ArrayList;

import org.apache.sysml.api.DMLScript;
import org.apache.sysml.hops.Hop.MultiThreadedHop;
import org.apache.sysml.hops.rewrite.HopRewriteUtils;
import org.apache.sysml.lops.Aggregate;
import org.apache.sysml.lops.Group;
import org.apache.sysml.lops.Lop;
import org.apache.sysml.lops.LopsException;
import org.apache.sysml.lops.SortKeys;
import org.apache.sysml.lops.Transform;
import org.apache.sysml.lops.LopProperties.ExecType;
import org.apache.sysml.lops.Transform.OperationTypes;
import org.apache.sysml.parser.Expression.DataType;
import org.apache.sysml.parser.Expression.ValueType;
import org.apache.sysml.runtime.matrix.MatrixCharacteristics;

/**
 *  Reorg (cell) operation: aij
 * 		Properties: 
 * 			Symbol: ', rdiag, rshape, rsort
 * 			1 Operand (except sort and reshape take additional arguments)
 * 	
 * 		Semantic: change indexes (in mapper or reducer)
 * 
 * 
 *  NOTE MB: reshape integrated here because (1) ParameterizedBuiltinOp requires name-value pairs for params
 *  and (2) most importantly semantic of reshape is exactly a reorg op. 
 */

public class ReorgOp extends Hop implements MultiThreadedHop
{
	public static boolean FORCE_DIST_SORT_INDEXES = false;
	
	private ReOrgOp op;
	private int _maxNumThreads = -1; //-1 for unlimited
	
	private ReorgOp() {
		//default constructor for clone
	}
	
	public ReorgOp(String l, DataType dt, ValueType vt, ReOrgOp o, Hop inp) 
	{
		super(l, dt, vt);
		op = o;
		getInput().add(0, inp);
		inp.getParent().add(this);
		
		//compute unknown dims and nnz
		refreshSizeInformation();
	}
	
	public ReorgOp(String l, DataType dt, ValueType vt, ReOrgOp o, ArrayList<Hop> inp) 
	{
		super(l, dt, vt);
		op = o;
		
		for( int i=0; i<inp.size(); i++ ) {
			Hop in = inp.get(i);
			getInput().add(i, in);
			in.getParent().add(this);
		}
		
		//compute unknown dims and nnz
		refreshSizeInformation();
	}

	@Override
	public void checkArity() throws HopsException {
		int sz = _input.size();
		switch( op ) {
		case TRANSPOSE:
		case DIAG:
		case REV:
			HopsException.check(sz == 1, this, "should have arity 1 for op %s but has arity %d", op, sz);
			break;
		case RESHAPE:
		case SORT:
			HopsException.check(sz == 4, this, "should have arity 4 for op %s but has arity %d", op, sz);
			break;
		default:
			throw new HopsException("Unsupported lops construction for operation type '" + op + "'.");
		}
	}

	@Override
	public void setMaxNumThreads( int k ) {
		_maxNumThreads = k;
	}
	
	@Override
	public int getMaxNumThreads() {
		return _maxNumThreads;
	}
	
	public ReOrgOp getOp()
	{
		return op;
	}
	
	@Override
	public String getOpString() {
		String s = new String("");
		s += "r(" + HopsTransf2String.get(op) + ")";
		return s;
	}
	
	@Override
	public boolean isGPUEnabled() {
		if(!DMLScript.USE_ACCELERATOR)
			return false;
		switch( op ) {
			case TRANSPOSE: {
				Lop lin;
				try {
					lin = getInput().get(0).constructLops();
				} catch (HopsException | LopsException e) {
					throw new RuntimeException("Unable to create child lop", e);
				}
				if( lin instanceof Transform && ((Transform)lin).getOperationType()==OperationTypes.Transpose )
					return false; //if input is already a transpose, avoid redundant transpose ops
				else if( getDim1()==1 && getDim2()==1 )
					return false; //if input of size 1x1, avoid unnecessary transpose
				else
					return true;
			}
			case DIAG:
			case REV:
			case RESHAPE:
			case SORT:
				return false;
			default:
				throw new RuntimeException("Unsupported operator:" + op.name());
		}
	}

	@Override
	public Lop constructLops()
		throws HopsException, LopsException 
	{
		//return already created lops
		if( getLops() != null )
			return getLops();

		ExecType et = optFindExecType();
		
		switch( op )
		{
			case TRANSPOSE:
			{
				Lop lin = getInput().get(0).constructLops();
				if( lin instanceof Transform && ((Transform)lin).getOperationType()==OperationTypes.Transpose )
					setLops(lin.getInputs().get(0)); //if input is already a transpose, avoid redundant transpose ops
				else if( getDim1()==1 && getDim2()==1 )
					setLops(lin); //if input of size 1x1, avoid unnecessary transpose
				else { //general case
					int k = OptimizerUtils.getConstrainedNumThreads(_maxNumThreads);
					Transform transform1 = new Transform( lin, 
							HopsTransf2Lops.get(op), getDataType(), getValueType(), et, k);
					setOutputDimensions(transform1);
					setLineNumbers(transform1);
					setLops(transform1);
				}
				break;
			}
			case DIAG:
			{
				Transform transform1 = new Transform( getInput().get(0).constructLops(), 
						HopsTransf2Lops.get(op), getDataType(), getValueType(), et);
				setOutputDimensions(transform1);
				setLineNumbers(transform1);
				setLops(transform1);
				
				break;
			}
			case REV:
			{
				Lop rev = null;
				
				if( et == ExecType.MR ) {
					Lop tmp = new Transform( getInput().get(0).constructLops(), 
							HopsTransf2Lops.get(op), getDataType(), getValueType(), et);
					setOutputDimensions(tmp);
					setLineNumbers(tmp);
						
					Group group1 = new Group(tmp, Group.OperationTypes.Sort, 
							DataType.MATRIX, getValueType());
					setOutputDimensions(group1);
					setLineNumbers(group1);
	
					rev = new Aggregate(group1, Aggregate.OperationTypes.Sum, 
							DataType.MATRIX, getValueType(), et);
				}
				else { //CP/SPARK

					rev = new Transform( getInput().get(0).constructLops(), 
						HopsTransf2Lops.get(op), getDataType(), getValueType(), et);
				}
				
				setOutputDimensions(rev);
				setLineNumbers(rev);
				setLops(rev);
				
				break;
			}
			case RESHAPE:
			{
				if( et==ExecType.MR )
				{
					Transform transform1 = new Transform( getInput().get(0).constructLops(), 
							HopsTransf2Lops.get(op), getDataType(), getValueType(), et);
					setOutputDimensions(transform1);
					setLineNumbers(transform1);
					for( int i=1; i<=3; i++ ) //rows, cols, byrow
					{
						Lop ltmp = getInput().get(i).constructLops();
						transform1.addInput(ltmp);
						ltmp.addOutput(transform1);
					}
					transform1.setLevel(); //force order of added lops
					
					Group group1 = new Group(
							transform1, Group.OperationTypes.Sort, DataType.MATRIX,
							getValueType());
					setOutputDimensions(group1);
					setLineNumbers(group1);
	
					Aggregate agg1 = new Aggregate(
							group1, Aggregate.OperationTypes.Sum, DataType.MATRIX,
							getValueType(), et);
					setOutputDimensions(agg1);
					setLineNumbers(agg1);
					
					setLops(agg1);
				}
				else //CP/SPARK
				{
					Transform transform1 = new Transform( getInput().get(0).constructLops(), 
							HopsTransf2Lops.get(op), getDataType(), getValueType(), et);
					setOutputDimensions(transform1);
					setLineNumbers(transform1);
					
					for( int i=1; i<=3; i++ ) //rows, cols, byrow
					{
						Lop ltmp = getInput().get(i).constructLops();
						transform1.addInput(ltmp);
						ltmp.addOutput(transform1);
					}
					transform1.setLevel(); //force order of added lops
					
					setLops(transform1);
				}
				break;
			}
			case SORT:
			{
				Hop input = getInput().get(0);
				Hop by = getInput().get(1);
				Hop desc = getInput().get(2);
				Hop ixret = getInput().get(3);
				
				if( et==ExecType.MR )
				{
					
					if( !(desc instanceof LiteralOp && ixret instanceof LiteralOp) ) {
						LOG.warn("Unsupported non-constant ordering parameters, using defaults and mark for recompilation.");
						setRequiresRecompile();
						desc = new LiteralOp(false);
						ixret = new LiteralOp(false);
					}
						
					//Step 1: extraction (if unknown ncol or multiple columns)
					Hop vinput = input;
					if( input.getDim2() != 1 ) {
						vinput = new IndexingOp("tmp1", getDataType(), getValueType(), input, new LiteralOp(1L), 
								HopRewriteUtils.createValueHop(input, true), by, by, false, true);
						vinput.refreshSizeInformation();
						vinput.setOutputBlocksizes(getRowsInBlock(), getColsInBlock());
						HopRewriteUtils.copyLineNumbers(this, vinput);	
					}
					
					//Step 2: Index vector sort 
					Hop voutput = null;
					if( 2*OptimizerUtils.estimateSize(vinput.getDim1(), vinput.getDim2())
						> OptimizerUtils.getLocalMemBudget() 
						|| FORCE_DIST_SORT_INDEXES ) 
					{ 
						//large vector, fallback to MR sort
						//sort indexes according to given values
						SortKeys sort = new SortKeys(
								vinput.constructLops(), HopRewriteUtils.getBooleanValueSafe((LiteralOp)desc), 
								SortKeys.OperationTypes.Indexes, 
								vinput.getDataType(), vinput.getValueType(), ExecType.MR);
			
						sort.getOutputParameters().setDimensions(vinput.getDim1(), 1, 
								vinput.getRowsInBlock(), vinput.getColsInBlock(), vinput.getNnz());
			
						setLineNumbers(sort);
						
						//note: this sortindexes includes also the shift by offsets and 
						//final aggregate because sideways passing of offsets would
						//not nicely fit the current instruction model
						
						setLops(sort);
						voutput = this;
					}
					else
					{
						//small vector, use in-memory sort
						ArrayList<Hop> sinputs = new ArrayList<>();
						sinputs.add(vinput);
						sinputs.add(new LiteralOp(1)); //by (always vector)
						sinputs.add(desc);
						sinputs.add(new LiteralOp(true)); //indexreturn (always indexes)
						voutput = new ReorgOp("tmp3", getDataType(), getValueType(), ReOrgOp.SORT, sinputs); 
						HopRewriteUtils.copyLineNumbers(this, voutput);	
						//explicitly construct CP lop; otherwise there is danger of infinite recursion if forced runtime platform.
						voutput.setLops( constructCPOrSparkSortLop(vinput, sinputs.get(1), sinputs.get(2), sinputs.get(3), ExecType.CP, false) );
						voutput.getLops().getOutputParameters().setDimensions(vinput.getDim1(), vinput.getDim2(), vinput.getRowsInBlock(), vinput.getColsInBlock(), vinput.getNnz());
						setLops( voutput.constructLops() );
					}
					
					//Step 3: Data permutation (only required for sorting data) 
					// -- done via X' = table(seq(), IX') %*% X;
					if( !HopRewriteUtils.getBooleanValueSafe((LiteralOp)ixret) ) 
					{
						//generate seq 
						DataGenOp seq = HopRewriteUtils.createSeqDataGenOp(voutput);
						seq.setName("tmp4");
						seq.refreshSizeInformation(); 
						seq.computeMemEstimate(new MemoTable()); //select exec type
						HopRewriteUtils.copyLineNumbers(this, seq);	
						
						//generate table
						TernaryOp table = new TernaryOp("tmp5", DataType.MATRIX, ValueType.DOUBLE, OpOp3.CTABLE, seq, voutput, new LiteralOp(1L) );
						table.setOutputBlocksizes(getRowsInBlock(), getColsInBlock());
						table.refreshSizeInformation();
						table.setForcedExecType(ExecType.MR); //force MR 
						HopRewriteUtils.copyLineNumbers(this, table);
						table.setDisjointInputs(true);
						table.setOutputEmptyBlocks(false);
						
						//generate matrix mult
						AggBinaryOp mmult = HopRewriteUtils.createMatrixMultiply(table, input);
						mmult.setForcedExecType(ExecType.MR); //force MR 
						
						setLops( mmult.constructLops() );
						
						//cleanups
						HopRewriteUtils.removeChildReference(table, input);
					}
				}
				else if( et==ExecType.SPARK ) {
					boolean sortRewrite = !FORCE_DIST_SORT_INDEXES 
						&& isSortSPRewriteApplicable() && by.getDataType().isScalar();
					Lop transform1 = constructCPOrSparkSortLop(input, by, desc, ixret, et, sortRewrite);
					setOutputDimensions(transform1);
					setLineNumbers(transform1);
					setLops(transform1);
				}
				else //CP
				{
					Lop transform1 = constructCPOrSparkSortLop(input, by, desc, ixret, et, false);
					setOutputDimensions(transform1);
					setLineNumbers(transform1);
					setLops(transform1);
				}
				break;
			}
			
			default: 
				throw new HopsException("Unsupported lops construction for operation type '"+op+"'.");
		}
		
		//add reblock/checkpoint lops if necessary
		constructAndSetLopsDataFlowProperties();
				
		return getLops();
	}

	private static Lop constructCPOrSparkSortLop( Hop input, Hop by, Hop desc, Hop ixret, ExecType et, boolean bSortIndInMem ) 
		throws HopsException, LopsException
	{
		Transform transform1 = new Transform( input.constructLops(), HopsTransf2Lops.get(ReOrgOp.SORT), 
				input.getDataType(), input.getValueType(), et, bSortIndInMem);
		
		for( Hop c : new Hop[]{by,desc,ixret} ) {
			Lop ltmp = c.constructLops();
			transform1.addInput(ltmp);
			ltmp.addOutput(transform1);
		}
		
		transform1.setLevel(); //force order of added lops
		
		return transform1;
	}
			
	@Override
	protected double computeOutputMemEstimate( long dim1, long dim2, long nnz )
	{		
		//no dedicated mem estimation per op type, because always propagated via refreshSizeInformation
		double sparsity = OptimizerUtils.getSparsity(dim1, dim2, nnz);
		return OptimizerUtils.estimateSizeExactSparsity(dim1, dim2, sparsity);
	}
	
	@Override
	protected double computeIntermediateMemEstimate( long dim1, long dim2, long nnz )
	{
		if( op == ReOrgOp.SORT ) 
		{
			Hop ixreturn = getInput().get(3);	
			if( !(ixreturn instanceof LiteralOp && !HopRewriteUtils.getBooleanValueSafe((LiteralOp)ixreturn)
				 && (dim2==1 || nnz==0) ) ) //NOT early abort case 
			{
				//Version 2: memory requirements for temporary index int[] array,
				//(temporary double[] array already covered by output)
				return dim1 * 4;
				
				//Version 1: memory requirements for temporary index Integer[] array
				//8-16 (12) bytes for object, 4byte int payload, 4-8 (8) byte pointers.
				//return dim1 * 24; 
			}
		}
		
		//default: no intermediate memory requirements
		return 0;
	}
	
	@Override
	protected long[] inferOutputCharacteristics( MemoTable memo )
	{
		long[] ret = null;
	
		Hop input = getInput().get(0);
		MatrixCharacteristics mc = memo.getAllInputStats(input);
			
		switch(op) 
		{
			case TRANSPOSE:
			{
				// input is a [k1,k2] matrix and output is a [k2,k1] matrix
				// #nnz in output is exactly the same as in input
				if( mc.dimsKnown() )
					ret = new long[]{ mc.getCols(), mc.getRows(), mc.getNonZeros() };
				break;
			}
			case REV:
			{
				// dims and nnz are exactly the same as in input
				if( mc.dimsKnown() )
					ret = new long[]{ mc.getRows(), mc.getCols(), mc.getNonZeros() };
				break;
			}
			case DIAG:
			{
				// NOTE: diag is overloaded according to the number of columns of the input
				
				long k = mc.getRows(); 
				
				// CASE a) DIAG V2M
				// input is a [1,k] or [k,1] matrix, and output is [k,k] matrix
				// #nnz in output is in the worst case k => sparsity = 1/k
				if( k == 1 )
					ret = new long[]{k, k, ((mc.getNonZeros()>=0) ? mc.getNonZeros() : k)};
				
				// CASE b) DIAG M2V
				// input is [k,k] matrix and output is [k,1] matrix
				// #nnz in the output is likely to be k (a dense matrix)		
				if( k > 1 )
					ret = new long[]{k, 1, ((mc.getNonZeros()>=0) ? Math.min(k,mc.getNonZeros()) : k) };
				
				break;		
			}
			case RESHAPE:
			{
				// input is a [k1,k2] matrix and output is a [k3,k4] matrix with k1*k2=k3*k4
				// #nnz in output is exactly the same as in input		
				if( mc.dimsKnown() ) {
					if( _dim1 > 0  )
						ret = new long[]{ _dim1, mc.getRows()*mc.getCols()/_dim1, mc.getNonZeros()};
					else if( _dim2 > 0 )	 
						ret = new long[]{ mc.getRows()*mc.getCols()/_dim2, _dim2, mc.getNonZeros()};
				}
				break;
			}
			case SORT:
			{
				// input is a [k1,k2] matrix and output is a [k1,k3] matrix, where k3=k2 if no index return;
				// otherwise k3=1 (for the index vector)	
				Hop input4 = getInput().get(3); //indexreturn
				boolean unknownIxRet = !(input4 instanceof LiteralOp);
				
				if( !unknownIxRet ) {
					boolean ixret = HopRewriteUtils.getBooleanValueSafe((LiteralOp)input4);
					long dim2 = ixret ? 1 : mc.getCols();
					long nnz = ixret ? mc.getRows() : mc.getNonZeros();
					ret = new long[]{ mc.getRows(), dim2, nnz};
				}
				else {
					ret = new long[]{ mc.getRows(), -1, -1};
				}
			}
		}	
		
		return ret;
	}
	

	@Override
	public boolean allowsAllExecTypes()
	{
		return true;
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
			// Choose CP, if the input dimensions are below threshold or if the input is a vector
			else if ( getInput().get(0).areDimsBelowThreshold() || getInput().get(0).isVector() )
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
	
	@Override
	public void refreshSizeInformation()
	{
		Hop input1 = getInput().get(0);
		
		switch(op) 
		{
			case TRANSPOSE:
			{
				// input is a [k1,k2] matrix and output is a [k2,k1] matrix
				// #nnz in output is exactly the same as in input
				setDim1(input1.getDim2());
				setDim2(input1.getDim1());
				setNnz(input1.getNnz());
				break;
			}
			case REV:
			{
				// dims and nnz are exactly the same as in input
				setDim1(input1.getDim1());
				setDim2(input1.getDim2());
				setNnz(input1.getNnz());
				break;
			}
			case DIAG:
			{
				// NOTE: diag is overloaded according to the number of columns of the input
				
				long k = input1.getDim1(); 
				setDim1(k);
				
				// CASE a) DIAG_V2M
				// input is a [1,k] or [k,1] matrix, and output is [k,k] matrix
				// #nnz in output is in the worst case k => sparsity = 1/k
				if( input1.getDim2()==1 ) {
					setDim2(k);
					setNnz( (input1.getNnz()>=0) ? input1.getNnz() : k );
				}
				
				// CASE b) DIAG_M2V
				// input is [k,k] matrix and output is [k,1] matrix
				// #nnz in the output is likely to be k (a dense matrix)		
				if( input1.getDim2()>1 ){
					setDim2(1);	
					setNnz( (input1.getNnz()>=0) ? Math.min(k,input1.getNnz()) : k );
				}
				
				break;		
			}
			case RESHAPE:
			{
				// input is a [k1,k2] matrix and output is a [k3,k4] matrix with k1*k2=k3*k4
				// #nnz in output is exactly the same as in input		
				Hop input2 = getInput().get(1); //rows 
				Hop input3 = getInput().get(2); //cols 
				refreshRowsParameterInformation(input2); //refresh rows
 				refreshColsParameterInformation(input3); //refresh cols
 				setNnz(input1.getNnz());
 				if( !dimsKnown() &&input1.dimsKnown() ) { //reshape allows to infer dims, if input and 1 dim known
	 				if(_dim1 > 0) 
						_dim2 = (input1._dim1*input1._dim2)/_dim1;
					else if(_dim2 > 0)	
						_dim1 = (input1._dim1*input1._dim2)/_dim2; 
 				}
				break;
			}
			case SORT:
			{
				// input is a [k1,k2] matrix and output is a [k1,k3] matrix, where k3=k2 if no index return;
				// otherwise k3=1 (for the index vector)
				Hop input4 = getInput().get(3); //indexreturn
				boolean unknownIxRet = !(input4 instanceof LiteralOp);
				
				_dim1 = input1.getDim1();
				if( !unknownIxRet ) {
					boolean ixret = HopRewriteUtils.getBooleanValueSafe((LiteralOp)input4);
					_dim2 = ixret ? 1 : input1.getDim2();
					_nnz = ixret ? input1.getDim1() : input1.getNnz();
				}
				else {
					_dim2 = -1;
					_nnz = -1;
				}
				break;
			}
		}	
	}
	
	@Override
	public Object clone() throws CloneNotSupportedException 
	{
		ReorgOp ret = new ReorgOp();	
		
		//copy generic attributes
		ret.clone(this, false);
		
		//copy specific attributes
		ret.op = op;
		ret._maxNumThreads = _maxNumThreads;
		
		return ret;
	}
	
	@Override
	public boolean compare( Hop that )
	{
		if( !(that instanceof ReorgOp) )
			return false;
		
		ReorgOp that2 = (ReorgOp)that;		
		boolean ret =  (op == that2.op)
				    && (_maxNumThreads == that2._maxNumThreads)
				    && (getInput().size()==that.getInput().size());
				
		//compare all childs (see reshape, sort)
		if( ret ) //sizes matched
			for( int i=0; i<_input.size(); i++ )
				ret &= getInput().get(i) == that2.getInput().get(i);
		
		return ret;
	}

	/**
	 * This will check if there is sufficient memory locally (twice the size of second matrix, for original and sort data), and remotely (size of second matrix (sorted data)).  
	 * @return true if sufficient memory locally
	 */
	private boolean isSortSPRewriteApplicable() 
	{
		boolean ret = false;
		Hop input = getInput().get(0);
		
		//note: both cases (partitioned matrix, and sorted double array), require to
		//fit the broadcast twice into the local memory budget. Also, the memory 
		//constraint only needs to take the rhs into account because the output is 
		//guaranteed to be an aggregate of <=16KB
		
		double size = input.dimsKnown() ? 
				OptimizerUtils.estimateSize(input.getDim1(), 1) : //dims known and estimate fits
					input.getOutputMemEstimate();                 //dims unknown but worst-case estimate fits
		
		if( OptimizerUtils.checkSparkBroadcastMemoryBudget(size) ) {
			ret = true;
		}
		
		return ret;
	}	
}

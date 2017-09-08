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

package org.apache.sysml.runtime.instructions.spark;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.apache.commons.lang3.ArrayUtils;
import org.apache.spark.api.java.JavaPairRDD;
import org.apache.spark.api.java.function.Function;
import org.apache.spark.api.java.function.Function2;
import org.apache.spark.api.java.function.PairFlatMapFunction;
import org.apache.spark.api.java.function.PairFunction;
import org.apache.sysml.hops.OptimizerUtils;
import org.apache.sysml.lops.PartialAggregate.CorrectionLocationType;
import org.apache.sysml.parser.Expression.DataType;
import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.codegen.CodegenUtils;
import org.apache.sysml.runtime.codegen.LibSpoofPrimitives;
import org.apache.sysml.runtime.codegen.SpoofCellwise;
import org.apache.sysml.runtime.codegen.SpoofCellwise.AggOp;
import org.apache.sysml.runtime.codegen.SpoofCellwise.CellType;
import org.apache.sysml.runtime.codegen.SpoofMultiAggregate;
import org.apache.sysml.runtime.codegen.SpoofOperator;
import org.apache.sysml.runtime.codegen.SpoofOuterProduct;
import org.apache.sysml.runtime.codegen.SpoofOuterProduct.OutProdType;
import org.apache.sysml.runtime.codegen.SpoofRowwise;
import org.apache.sysml.runtime.codegen.SpoofRowwise.RowType;
import org.apache.sysml.runtime.controlprogram.context.ExecutionContext;
import org.apache.sysml.runtime.controlprogram.context.SparkExecutionContext;
import org.apache.sysml.runtime.functionobjects.Builtin;
import org.apache.sysml.runtime.functionobjects.Builtin.BuiltinCode;
import org.apache.sysml.runtime.functionobjects.KahanPlus;
import org.apache.sysml.runtime.instructions.InstructionUtils;
import org.apache.sysml.runtime.instructions.cp.CPOperand;
import org.apache.sysml.runtime.instructions.cp.DoubleObject;
import org.apache.sysml.runtime.instructions.cp.ScalarObject;
import org.apache.sysml.runtime.instructions.spark.data.PartitionedBroadcast;
import org.apache.sysml.runtime.instructions.spark.functions.ReplicateBlockFunction;
import org.apache.sysml.runtime.instructions.spark.utils.RDDAggregateUtils;
import org.apache.sysml.runtime.matrix.MatrixCharacteristics;
import org.apache.sysml.runtime.matrix.data.MatrixBlock;
import org.apache.sysml.runtime.matrix.data.MatrixIndexes;
import org.apache.sysml.runtime.matrix.operators.AggregateOperator;

import scala.Tuple2;

public class SpoofSPInstruction extends SPInstruction {
	private final Class<?> _class;
	private final byte[] _classBytes;
	private final CPOperand[] _in;
	private final CPOperand _out;

	private SpoofSPInstruction(Class<?> cls, byte[] classBytes, CPOperand[] in, CPOperand out, String opcode,
			String str) {
		super(opcode, str);
		_class = cls;
		_classBytes = classBytes;
		_sptype = SPINSTRUCTION_TYPE.SpoofFused;
		_in = in;
		_out = out;
	}

	public static SpoofSPInstruction parseInstruction(String str) 
		throws DMLRuntimeException
	{
		String[] parts = InstructionUtils.getInstructionPartsWithValueType(str);
		
		//String opcode = parts[0];
		ArrayList<CPOperand> inlist = new ArrayList<CPOperand>();
		Class<?> cls = CodegenUtils.getClass(parts[1]);
		byte[] classBytes = CodegenUtils.getClassData(parts[1]);
		String opcode =  parts[0] + CodegenUtils.createInstance(cls).getSpoofType();
		
		for( int i=2; i<parts.length-2; i++ )
			inlist.add(new CPOperand(parts[i]));
		CPOperand out = new CPOperand(parts[parts.length-2]);
		//note: number of threads parts[parts.length-1] always ignored
		
		return new SpoofSPInstruction(cls, classBytes, inlist.toArray(new CPOperand[0]), out, opcode, str);
	}

	@Override
	public void processInstruction(ExecutionContext ec)
		throws DMLRuntimeException 
	{	
		SparkExecutionContext sec = (SparkExecutionContext)ec;
		
		//decide upon broadcast side inputs
		boolean[] bcVect = determineBroadcastInputs(sec, _in);
		boolean[] bcVect2 = getMatrixBroadcastVector(sec, _in, bcVect);
		
		//create joined input rdd w/ replication if needed
		MatrixCharacteristics mcIn = sec.getMatrixCharacteristics(_in[0].getName());
		JavaPairRDD<MatrixIndexes, MatrixBlock[]> in = createJoinedInputRDD(
			sec, _in, bcVect, (_class.getSuperclass() == SpoofOuterProduct.class));
		JavaPairRDD<MatrixIndexes, MatrixBlock> out = null;
		
		//create lists of input broadcasts and scalars
		ArrayList<PartitionedBroadcast<MatrixBlock>> bcMatrices = new ArrayList<>();
		ArrayList<ScalarObject> scalars = new ArrayList<>();
		for( int i=1; i<_in.length; i++ ) {
			if( _in[i].getDataType()==DataType.MATRIX && bcVect[i] ) {
				bcMatrices.add(sec.getBroadcastForVariable(_in[i].getName()));
			}
			else if(_in[i].getDataType()==DataType.SCALAR) {
				//note: even if literal, it might be compiled as scalar placeholder
				scalars.add(sec.getScalarInput(_in[i].getName(), _in[i].getValueType(), _in[i].isLiteral()));
			}
		}
		
		//execute generated operator
		if(_class.getSuperclass() == SpoofCellwise.class) //CELL
		{
			SpoofCellwise op = (SpoofCellwise) CodegenUtils.createInstance(_class); 	
			AggregateOperator aggop = getAggregateOperator(op.getAggOp());
			
			if( _out.getDataType()==DataType.MATRIX ) {
				//execute codegen block operation
				out = in.mapPartitionsToPair(new CellwiseFunction(
					_class.getName(), _classBytes, bcVect2, bcMatrices, scalars), true);
				
				if( (op.getCellType()==CellType.ROW_AGG && mcIn.getCols() > mcIn.getColsPerBlock())
					|| (op.getCellType()==CellType.COL_AGG && mcIn.getRows() > mcIn.getRowsPerBlock())) {
					//TODO investigate if some other side effect of correct blocks
					long numBlocks = (op.getCellType()==CellType.ROW_AGG ) ? 
						mcIn.getNumRowBlocks() : mcIn.getNumColBlocks();
					if( out.partitions().size() > numBlocks )
						out = RDDAggregateUtils.aggByKeyStable(out, aggop, (int)numBlocks, false);
					else
						out = RDDAggregateUtils.aggByKeyStable(out, aggop, false);
				}
				sec.setRDDHandleForVariable(_out.getName(), out);
				
				//maintain lineage info and output characteristics
				maintainLineageInfo(sec, _in, bcVect, _out);
				updateOutputMatrixCharacteristics(sec, op);	
			}
			else { //SCALAR
				out = in.mapPartitionsToPair(new CellwiseFunction(
					_class.getName(), _classBytes, bcVect2, bcMatrices, scalars), true);
				MatrixBlock tmpMB = RDDAggregateUtils.aggStable(out, aggop);
				sec.setVariable(_out.getName(), new DoubleObject(tmpMB.getValue(0, 0)));
			}
		}
		else if(_class.getSuperclass() == SpoofMultiAggregate.class) //MAGG
		{
			SpoofMultiAggregate op = (SpoofMultiAggregate) CodegenUtils.createInstance(_class); 	
			AggOp[] aggOps = op.getAggOps();
			
			MatrixBlock tmpMB = in.mapToPair(new MultiAggregateFunction(
				_class.getName(), _classBytes,  bcVect2, bcMatrices, scalars))
				.values().fold(new MatrixBlock(), new MultiAggAggregateFunction(aggOps) );
			
			sec.setMatrixOutput(_out.getName(), tmpMB, getExtendedOpcode());
		}
		else if(_class.getSuperclass() == SpoofOuterProduct.class) //OUTER
		{
			if( _out.getDataType()==DataType.MATRIX ) {
				SpoofOperator op = (SpoofOperator) CodegenUtils.createInstance(_class); 	
				OutProdType type = ((SpoofOuterProduct)op).getOuterProdType();

				//update matrix characteristics
				updateOutputMatrixCharacteristics(sec, op);			
				MatrixCharacteristics mcOut = sec.getMatrixCharacteristics(_out.getName());
				
				out = in.mapPartitionsToPair(new OuterProductFunction(
					_class.getName(), _classBytes, bcVect2, bcMatrices, scalars), true);
				if(type == OutProdType.LEFT_OUTER_PRODUCT || type == OutProdType.RIGHT_OUTER_PRODUCT ) {
					//TODO investigate if some other side effect of correct blocks
					if( in.partitions().size() > mcOut.getNumRowBlocks()*mcOut.getNumColBlocks() )
						out = RDDAggregateUtils.sumByKeyStable(out, (int)(mcOut.getNumRowBlocks()*mcOut.getNumColBlocks()), false);
					else
						out = RDDAggregateUtils.sumByKeyStable(out, false);	
				}
				sec.setRDDHandleForVariable(_out.getName(), out);
				
				//maintain lineage info and output characteristics
				maintainLineageInfo(sec, _in, bcVect, _out);
			}
			else {
				out = in.mapPartitionsToPair(new OuterProductFunction(
					_class.getName(), _classBytes, bcVect2, bcMatrices, scalars), true);
				MatrixBlock tmp = RDDAggregateUtils.sumStable(out);
				sec.setVariable(_out.getName(), new DoubleObject(tmp.getValue(0, 0)));
			}
		}
		else if( _class.getSuperclass() == SpoofRowwise.class ) { //ROW
			if( mcIn.getCols() > mcIn.getColsPerBlock() ) {
				throw new DMLRuntimeException("Invalid spark rowwise operator w/ ncol=" + 
					mcIn.getCols()+", ncolpb="+mcIn.getColsPerBlock()+".");
			}
			SpoofRowwise op = (SpoofRowwise) CodegenUtils.createInstance(_class); 	
			RowwiseFunction fmmc = new RowwiseFunction(_class.getName(),
				_classBytes, bcVect2, bcMatrices, scalars, (int)mcIn.getCols());
			out = in.mapPartitionsToPair(fmmc, op.getRowType()==RowType.ROW_AGG
					|| op.getRowType() == RowType.NO_AGG);
			
			if( op.getRowType().isColumnAgg() || op.getRowType()==RowType.FULL_AGG ) {
				MatrixBlock tmpMB = RDDAggregateUtils.sumStable(out);
				if( op.getRowType().isColumnAgg() )
					sec.setMatrixOutput(_out.getName(), tmpMB, getExtendedOpcode());
				else
					sec.setScalarOutput(_out.getName(), 
						new DoubleObject(tmpMB.quickGetValue(0, 0)));
			}
			else //row-agg or no-agg 
			{
				if( op.getRowType()==RowType.ROW_AGG && mcIn.getCols() > mcIn.getColsPerBlock() ) {
					//TODO investigate if some other side effect of correct blocks
					if( out.partitions().size() > mcIn.getNumRowBlocks() )
						out = RDDAggregateUtils.sumByKeyStable(out, (int)mcIn.getNumRowBlocks(), false);
					else
						out = RDDAggregateUtils.sumByKeyStable(out, false);
				}
				
				sec.setRDDHandleForVariable(_out.getName(), out);
				
				//maintain lineage info and output characteristics
				maintainLineageInfo(sec, _in, bcVect, _out);
				updateOutputMatrixCharacteristics(sec, op);
			}
		}
		else {
			throw new DMLRuntimeException("Operator " + _class.getSuperclass() + " is not supported on Spark");
		}
	}
	
	private static boolean[] determineBroadcastInputs(SparkExecutionContext sec, CPOperand[] inputs) 
		throws DMLRuntimeException 
	{
		boolean[] ret = new boolean[inputs.length];
		double localBudget = OptimizerUtils.getLocalMemBudget();
		double bcBudget = SparkExecutionContext.getBroadcastMemoryBudget();
		
		//decided for each matrix input if it fits into remaining memory
		//budget; the major input, i.e., inputs[0] is always an RDD
		for( int i=1; i<inputs.length; i++ ) 
			if( inputs[i].getDataType().isMatrix() ) {
				MatrixCharacteristics mc = sec.getMatrixCharacteristics(inputs[i].getName());
				double sizeL = OptimizerUtils.estimateSizeExactSparsity(mc);
				double sizeP = OptimizerUtils.estimatePartitionedSizeExactSparsity(mc);
				ret[i] = localBudget > sizeL && bcBudget > sizeP;
				localBudget -= ret[i] ? sizeL : 0;
				bcBudget -= ret[i] ? sizeP : 0;
			}
		
		return ret;
	}
	
	private static boolean[] getMatrixBroadcastVector(SparkExecutionContext sec, CPOperand[] inputs, boolean[] bcVect) 
			throws DMLRuntimeException 
	{
		int numMtx = (int) Arrays.stream(inputs)
			.filter(in -> in.getDataType().isMatrix()).count();
		boolean[] ret = new boolean[numMtx];
		for(int i=0, pos=0; i<inputs.length; i++)
			if( inputs[i].getDataType().isMatrix() )
				ret[pos++] = bcVect[i];
		return ret;
	}
	
	private static JavaPairRDD<MatrixIndexes, MatrixBlock[]> createJoinedInputRDD(SparkExecutionContext sec, CPOperand[] inputs, boolean[] bcVect, boolean outer) 
		throws DMLRuntimeException
	{
		//get input rdd for main input
		MatrixCharacteristics mcIn = sec.getMatrixCharacteristics(inputs[0].getName());
		JavaPairRDD<MatrixIndexes, MatrixBlock> in = sec.getBinaryBlockRDDHandleForVariable(inputs[0].getName());
		JavaPairRDD<MatrixIndexes, MatrixBlock[]> ret = in.mapValues(new MapInputSignature());
		
		for( int i=1; i<inputs.length; i++ )
			if( inputs[i].getDataType().isMatrix() && !bcVect[i] ) {
				//create side input rdd 
				String varname = inputs[i].getName();
				JavaPairRDD<MatrixIndexes, MatrixBlock> tmp = sec
					.getBinaryBlockRDDHandleForVariable(varname);
				MatrixCharacteristics mcTmp = sec.getMatrixCharacteristics(varname);
				//replicate blocks if mismatch with main input
				if( outer && i==2 )
					tmp = tmp.flatMapToPair(new ReplicateRightFactorFunction(mcIn.getRows(), mcIn.getRowsPerBlock()));
				else if( mcIn.getNumRowBlocks() > mcTmp.getNumRowBlocks() )
					tmp = tmp.flatMapToPair(new ReplicateBlockFunction(mcIn.getRows(), mcIn.getRowsPerBlock(), false));
				else if( mcIn.getNumColBlocks() > mcTmp.getNumColBlocks() )
					tmp = tmp.flatMapToPair(new ReplicateBlockFunction(mcIn.getCols(), mcIn.getColsPerBlock(), true));
				//join main and side inputs and consolidate signature
				ret = ret.join(tmp)
					.mapValues(new MapJoinSignature());
			}
		
		return ret;
	}
	
	private static void maintainLineageInfo(SparkExecutionContext sec, CPOperand[] inputs, boolean[] bcVect, CPOperand output) 
		throws DMLRuntimeException 
	{
		//add lineage info for all rdd/broadcast inputs 
		for( int i=0; i<inputs.length; i++ )
			if( inputs[i].getDataType().isMatrix() )
				sec.addLineage(output.getName(), inputs[i].getName(), bcVect[i]);
	}
	
	private void updateOutputMatrixCharacteristics(SparkExecutionContext sec, SpoofOperator op) 
		throws DMLRuntimeException 
	{
		if(op instanceof SpoofCellwise)
		{
			MatrixCharacteristics mcIn = sec.getMatrixCharacteristics(_in[0].getName());
			MatrixCharacteristics mcOut = sec.getMatrixCharacteristics(_out.getName());
			if( ((SpoofCellwise)op).getCellType()==CellType.ROW_AGG )
				mcOut.set(mcIn.getRows(), 1, mcIn.getRowsPerBlock(), mcIn.getColsPerBlock());
			else if( ((SpoofCellwise)op).getCellType()==CellType.NO_AGG )
				mcOut.set(mcIn);
		}
		else if(op instanceof SpoofOuterProduct)
		{
			MatrixCharacteristics mcIn1 = sec.getMatrixCharacteristics(_in[0].getName()); //X
			MatrixCharacteristics mcIn2 = sec.getMatrixCharacteristics(_in[1].getName()); //U
			MatrixCharacteristics mcIn3 = sec.getMatrixCharacteristics(_in[2].getName()); //V
			MatrixCharacteristics mcOut = sec.getMatrixCharacteristics(_out.getName());
			OutProdType type = ((SpoofOuterProduct)op).getOuterProdType();
			
			if( type == OutProdType.CELLWISE_OUTER_PRODUCT)
				mcOut.set(mcIn1.getRows(), mcIn1.getCols(), mcIn1.getRowsPerBlock(), mcIn1.getColsPerBlock());
			else if( type == OutProdType.LEFT_OUTER_PRODUCT) 		
				mcOut.set(mcIn3.getRows(), mcIn3.getCols(), mcIn3.getRowsPerBlock(), mcIn3.getColsPerBlock());		
			else if( type == OutProdType.RIGHT_OUTER_PRODUCT )
				mcOut.set(mcIn2.getRows(), mcIn2.getCols(), mcIn2.getRowsPerBlock(), mcIn2.getColsPerBlock());
		}
		else if(op instanceof SpoofRowwise) {
			MatrixCharacteristics mcIn = sec.getMatrixCharacteristics(_in[0].getName());
			MatrixCharacteristics mcOut = sec.getMatrixCharacteristics(_out.getName());
			RowType type = ((SpoofRowwise)op).getRowType();
			if( type == RowType.NO_AGG )
				mcOut.set(mcIn);
			else if( type == RowType.ROW_AGG )
				mcOut.set(mcIn.getRows(), ((SpoofRowwise)op).isCBind0()? 2:1, 
					mcIn.getRowsPerBlock(), mcIn.getColsPerBlock());
			else if( type == RowType.COL_AGG )
				mcOut.set(1, mcIn.getCols(), mcIn.getRowsPerBlock(), mcIn.getColsPerBlock());
			else if( type == RowType.COL_AGG_T )
				mcOut.set(mcIn.getCols(), 1, mcIn.getRowsPerBlock(), mcIn.getColsPerBlock());
		}
	}
	
	private static class MapInputSignature implements Function<MatrixBlock, MatrixBlock[]> 
	{
		private static final long serialVersionUID = -816443970067626102L;
		
		@Override
		public MatrixBlock[] call(MatrixBlock v1) throws Exception {
			return new MatrixBlock[]{ v1 };
		}
	}
	
	private static class MapJoinSignature implements Function<Tuple2<MatrixBlock[],MatrixBlock>, MatrixBlock[]> 
	{
		private static final long serialVersionUID = -704403012606821854L;

		@Override
		public MatrixBlock[] call(Tuple2<MatrixBlock[], MatrixBlock> v1) throws Exception {
			return ArrayUtils.add(v1._1(), v1._2());
		}
	}
	
	private static class SpoofFunction implements Serializable 
	{	
		private static final long serialVersionUID = 2953479427746463003L;
		
		protected final boolean[] _bcInd;
		protected final ArrayList<PartitionedBroadcast<MatrixBlock>> _inputs;
		protected final ArrayList<ScalarObject> _scalars;
		protected final byte[] _classBytes;
		protected final String _className;
		
		protected SpoofFunction(String className, byte[] classBytes, boolean[] bcInd, ArrayList<PartitionedBroadcast<MatrixBlock>> bcMatrices, ArrayList<ScalarObject> scalars) {
			_bcInd = bcInd;
			_inputs = bcMatrices;
			_scalars = scalars;
			_classBytes = classBytes;
			_className = className;
		}
		
		protected ArrayList<MatrixBlock> getAllMatrixInputs(MatrixIndexes ixIn, MatrixBlock[] blkIn) 
			throws DMLRuntimeException 
		{
			return getAllMatrixInputs(ixIn, blkIn, false);
		}
		
		protected ArrayList<MatrixBlock> getAllMatrixInputs(MatrixIndexes ixIn, MatrixBlock[] blkIn, boolean outer) 
			throws DMLRuntimeException 
		{
			ArrayList<MatrixBlock> ret = new ArrayList<MatrixBlock>();
			//add all rdd/broadcast inputs (main and side inputs)
			for( int i=0, posRdd=0, posBc=0; i<_bcInd.length; i++ ) {
				if( _bcInd[i] ) {
					PartitionedBroadcast<MatrixBlock> pb = _inputs.get(posBc++);
					int rowIndex = (int) ((outer && i==2) ? ixIn.getColumnIndex() : 
						(pb.getNumRowBlocks()>=ixIn.getRowIndex())?ixIn.getRowIndex():1);
					int colIndex = (int) ((outer && i==2) ? 1 : 
						(pb.getNumColumnBlocks()>=ixIn.getColumnIndex())?ixIn.getColumnIndex():1);
					ret.add(pb.getBlock(rowIndex, colIndex));
				}
				else
					ret.add(blkIn[posRdd++]);
			}
			return ret;
		}
	}
	
	private static class RowwiseFunction extends SpoofFunction
		implements PairFlatMapFunction<Iterator<Tuple2<MatrixIndexes, MatrixBlock[]>>, MatrixIndexes, MatrixBlock> 
	{
		private static final long serialVersionUID = -7926980450209760212L;

		private final int _clen;
		private SpoofRowwise _op = null;
		
		public RowwiseFunction(String className, byte[] classBytes, boolean[] bcInd, ArrayList<PartitionedBroadcast<MatrixBlock>> bcMatrices, ArrayList<ScalarObject> scalars, int clen) 
			throws DMLRuntimeException
		{			
			super(className, classBytes, bcInd, bcMatrices, scalars);
			_clen = clen;
		}
		
		@Override
		public Iterator<Tuple2<MatrixIndexes, MatrixBlock>> call( Iterator<Tuple2<MatrixIndexes, MatrixBlock[]>> arg ) 
			throws Exception 
		{
			//lazy load of shipped class
			if( _op == null ) {
				Class<?> loadedClass = CodegenUtils.getClass(_className, _classBytes);
				_op = (SpoofRowwise) CodegenUtils.createInstance(loadedClass); 
			}
			
			//setup local memory for reuse
			int clen2 = (int) (_op.getRowType().isRowTypeB1() ? _inputs.get(0).getNumCols() : -1);
			LibSpoofPrimitives.setupThreadLocalMemory(_op.getNumIntermediates(), _clen, clen2);
			
			ArrayList<Tuple2<MatrixIndexes,MatrixBlock>> ret = new ArrayList<Tuple2<MatrixIndexes,MatrixBlock>>();
			boolean aggIncr = (_op.getRowType().isColumnAgg() //aggregate entire partition
				|| _op.getRowType() == RowType.FULL_AGG); 
			MatrixBlock blkOut = aggIncr ? new MatrixBlock() : null;
			
			while( arg.hasNext() ) {
				//get main input block and indexes
				Tuple2<MatrixIndexes,MatrixBlock[]> e = arg.next();
				MatrixIndexes ixIn = e._1();
				MatrixBlock[] blkIn = e._2();
				
				//prepare output and execute single-threaded operator
				ArrayList<MatrixBlock> inputs = getAllMatrixInputs(ixIn, blkIn);
				blkOut = aggIncr ? blkOut : new MatrixBlock();
				blkOut = _op.execute(inputs, _scalars, blkOut, false, aggIncr);
				if( !aggIncr ) {
					MatrixIndexes ixOut = new MatrixIndexes(ixIn.getRowIndex(),
						_op.getRowType()!=RowType.NO_AGG ? 1 : ixIn.getColumnIndex());
					ret.add(new Tuple2<MatrixIndexes, MatrixBlock>(ixOut, blkOut));
				}
			}
			
			//cleanup and final result preparations
			LibSpoofPrimitives.cleanupThreadLocalMemory();
			if( aggIncr )
				ret.add(new Tuple2<MatrixIndexes, MatrixBlock>(new MatrixIndexes(1,1), blkOut));
			
			return ret.iterator();
		}
	}
	
	private static class CellwiseFunction extends SpoofFunction
		implements PairFlatMapFunction<Iterator<Tuple2<MatrixIndexes, MatrixBlock[]>>, MatrixIndexes, MatrixBlock> 
	{
		private static final long serialVersionUID = -8209188316939435099L;
		
		private SpoofOperator _op = null;
		
		public CellwiseFunction(String className, byte[] classBytes, boolean[] bcInd, ArrayList<PartitionedBroadcast<MatrixBlock>> bcMatrices, ArrayList<ScalarObject> scalars) 
			throws DMLRuntimeException
		{
			super(className, classBytes, bcInd, bcMatrices, scalars);
		}
		
		@Override
		public Iterator<Tuple2<MatrixIndexes, MatrixBlock>> call(Iterator<Tuple2<MatrixIndexes, MatrixBlock[]>> arg)
			throws Exception 
		{
			//lazy load of shipped class
			if( _op == null ) {
				Class<?> loadedClass = CodegenUtils.getClass(_className, _classBytes);
				_op = (SpoofOperator) CodegenUtils.createInstance(loadedClass); 
			}
			
			List<Tuple2<MatrixIndexes, MatrixBlock>> ret = new ArrayList<Tuple2<MatrixIndexes,MatrixBlock>>();
			while(arg.hasNext()) 
			{
				Tuple2<MatrixIndexes,MatrixBlock[]> tmp = arg.next();
				MatrixIndexes ixIn = tmp._1();
				MatrixBlock[] blkIn = tmp._2();
				MatrixIndexes ixOut = ixIn; 
				MatrixBlock blkOut = new MatrixBlock();
				ArrayList<MatrixBlock> inputs = getAllMatrixInputs(ixIn, blkIn);
				
				//execute core operation
				if(((SpoofCellwise)_op).getCellType()==CellType.FULL_AGG) {
					ScalarObject obj = _op.execute(inputs, _scalars, 1);
					blkOut.reset(1, 1);
					blkOut.quickSetValue(0, 0, obj.getDoubleValue());	
				}
				else {
					if(((SpoofCellwise)_op).getCellType()==CellType.ROW_AGG)
						ixOut = new MatrixIndexes(ixOut.getRowIndex(), 1);
					else if(((SpoofCellwise)_op).getCellType()==CellType.COL_AGG)
						ixOut = new MatrixIndexes(1, ixOut.getColumnIndex());
					blkOut = _op.execute(inputs, _scalars, blkOut);
				}
				ret.add(new Tuple2<MatrixIndexes,MatrixBlock>(ixOut, blkOut));
			}
			return ret.iterator();
		}
	}
	
	private static class MultiAggregateFunction extends SpoofFunction
		implements PairFunction<Tuple2<MatrixIndexes, MatrixBlock[]>, MatrixIndexes, MatrixBlock> 
	{
		private static final long serialVersionUID = -5224519291577332734L;
		
		private SpoofOperator _op = null;
		
		public MultiAggregateFunction(String className, byte[] classBytes, boolean[] bcInd, ArrayList<PartitionedBroadcast<MatrixBlock>> bcMatrices, ArrayList<ScalarObject> scalars) 
			throws DMLRuntimeException
		{
			super(className, classBytes, bcInd, bcMatrices, scalars);
		}
		
		@Override
		public Tuple2<MatrixIndexes, MatrixBlock> call(Tuple2<MatrixIndexes, MatrixBlock[]> arg)
			throws Exception 
		{
			//lazy load of shipped class
			if( _op == null ) {
				Class<?> loadedClass = CodegenUtils.getClass(_className, _classBytes);
				_op = (SpoofOperator) CodegenUtils.createInstance(loadedClass); 
			}
				
			//execute core operation
			ArrayList<MatrixBlock> inputs = getAllMatrixInputs(arg._1(), arg._2());
			MatrixBlock blkOut = new MatrixBlock();
			blkOut = _op.execute(inputs, _scalars, blkOut);
			
			return new Tuple2<MatrixIndexes,MatrixBlock>(arg._1(), blkOut);
		}
	}
	
	private static class MultiAggAggregateFunction implements Function2<MatrixBlock, MatrixBlock, MatrixBlock> 
	{
		private static final long serialVersionUID = 5978731867787952513L;
		
		private AggOp[] _ops = null;
		
		public MultiAggAggregateFunction( AggOp[] ops ) {
			_ops = ops;	
		}
		
		@Override
		public MatrixBlock call(MatrixBlock arg0, MatrixBlock arg1)
			throws Exception 
		{
			//prepare combiner block
			if( arg0.getNumRows() <= 0 || arg0.getNumColumns() <= 0) {
				arg0.copy(arg1);
				return arg0;
			}
			else if( arg1.getNumRows() <= 0 || arg1.getNumColumns() <= 0 ) {
				return arg0;
			}
			
			//aggregate second input (in-place)
			SpoofMultiAggregate.aggregatePartialResults(_ops, arg0, arg1);
			
			return arg0;
		}
	}
	
	private static class OuterProductFunction extends SpoofFunction
		implements PairFlatMapFunction<Iterator<Tuple2<MatrixIndexes, MatrixBlock[]>>, MatrixIndexes, MatrixBlock> 
	{
		private static final long serialVersionUID = -8209188316939435099L;
		
		private SpoofOperator _op = null;
		
		public OuterProductFunction(String className, byte[] classBytes, boolean[] bcInd, ArrayList<PartitionedBroadcast<MatrixBlock>> bcMatrices, ArrayList<ScalarObject> scalars) 
				throws DMLRuntimeException
		{
			super(className, classBytes, bcInd, bcMatrices, scalars);
		}
		
		@Override
		public Iterator<Tuple2<MatrixIndexes, MatrixBlock>> call(Iterator<Tuple2<MatrixIndexes, MatrixBlock[]>> arg)
			throws Exception 
		{
			//lazy load of shipped class
			if( _op == null ) {
				Class<?> loadedClass = CodegenUtils.getClass(_className, _classBytes);
				_op = (SpoofOperator) CodegenUtils.createInstance(loadedClass); 
			}
			
			List<Tuple2<MatrixIndexes, MatrixBlock>> ret = new ArrayList<Tuple2<MatrixIndexes,MatrixBlock>>();
			while(arg.hasNext())
			{
				Tuple2<MatrixIndexes,MatrixBlock[]> tmp = arg.next();
				MatrixIndexes ixIn = tmp._1();
				MatrixBlock[] blkIn = tmp._2();
				MatrixBlock blkOut = new MatrixBlock();

				ArrayList<MatrixBlock> inputs = getAllMatrixInputs(ixIn, blkIn, true);
				//execute core operation
				if(((SpoofOuterProduct)_op).getOuterProdType()==OutProdType.AGG_OUTER_PRODUCT) {
					ScalarObject obj = _op.execute(inputs, _scalars,1);
					blkOut.reset(1, 1);
					blkOut.quickSetValue(0, 0, obj.getDoubleValue());
				}
				else {
					blkOut = _op.execute(inputs, _scalars, blkOut);
				}
				
				ret.add(new Tuple2<MatrixIndexes,MatrixBlock>(createOutputIndexes(ixIn,_op), blkOut));				
			}
			
			return ret.iterator();
		}
		
		private MatrixIndexes createOutputIndexes(MatrixIndexes in, SpoofOperator spoofOp) {
			if( ((SpoofOuterProduct)spoofOp).getOuterProdType() == OutProdType.LEFT_OUTER_PRODUCT ) 
				return new MatrixIndexes(in.getColumnIndex(), 1);
			else if ( ((SpoofOuterProduct)spoofOp).getOuterProdType() == OutProdType.RIGHT_OUTER_PRODUCT)
				return new MatrixIndexes(in.getRowIndex(), 1);
			else 
				return in;
		}		
	}
	
	public static class ReplicateRightFactorFunction implements PairFlatMapFunction<Tuple2<MatrixIndexes, MatrixBlock>, MatrixIndexes, MatrixBlock> 
	{
		private static final long serialVersionUID = -7295989688796126442L;
		
		private final long _len;
		private final long _blen;
		
		public ReplicateRightFactorFunction(long len, long blen) {
			_len = len;
			_blen = blen;
		}
		
		@Override
		public Iterator<Tuple2<MatrixIndexes, MatrixBlock>> call( Tuple2<MatrixIndexes, MatrixBlock> arg0 ) 
			throws Exception 
		{
			LinkedList<Tuple2<MatrixIndexes, MatrixBlock>> ret = new LinkedList<Tuple2<MatrixIndexes, MatrixBlock>>();
			MatrixIndexes ixIn = arg0._1();
			MatrixBlock blkIn = arg0._2();
			
			long numBlocks = (long) Math.ceil((double)_len/_blen); 
			
			//replicate wrt # row blocks in LHS
			long j = ixIn.getRowIndex();
			for( long i=1; i<=numBlocks; i++ ) {
				MatrixIndexes tmpix = new MatrixIndexes(i, j);
				MatrixBlock tmpblk = blkIn;
				ret.add( new Tuple2<MatrixIndexes, MatrixBlock>(tmpix, tmpblk) );
			}
			
			//output list of new tuples
			return ret.iterator();
		}
	}
	
	public static AggregateOperator getAggregateOperator(AggOp aggop) {
		if( aggop == AggOp.SUM || aggop == AggOp.SUM_SQ )
			return new AggregateOperator(0, KahanPlus.getKahanPlusFnObject(), true, CorrectionLocationType.NONE);
		else if( aggop == AggOp.MIN )
			return new AggregateOperator(Double.MAX_VALUE, Builtin.getBuiltinFnObject(BuiltinCode.MIN), false, CorrectionLocationType.NONE);
		else if( aggop == AggOp.MAX )
			return new AggregateOperator(-Double.MAX_VALUE, Builtin.getBuiltinFnObject(BuiltinCode.MAX), false, CorrectionLocationType.NONE);
		return null;
	}
}

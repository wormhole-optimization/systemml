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

package org.apache.sysml.hops.codegen;

import java.util.ArrayList;

import org.apache.sysml.hops.Hop;
import org.apache.sysml.hops.Hop.MultiThreadedHop;
import org.apache.sysml.hops.MemoTable;
import org.apache.sysml.hops.OptimizerUtils;
import org.apache.sysml.lops.Lop;
import org.apache.sysml.lops.LopProperties.ExecType;
import org.apache.sysml.lops.SpoofFused;
import org.apache.sysml.parser.Expression.DataType;
import org.apache.sysml.parser.Expression.ValueType;
import org.apache.sysml.runtime.codegen.SpoofRowwise;
import org.apache.sysml.runtime.matrix.MatrixCharacteristics;

public class SpoofFusedOp extends Hop implements MultiThreadedHop
{
	public enum SpoofOutputDimsType {
		INPUT_DIMS,
		INPUT_DIMS_CONST2,
		ROW_DIMS,
		COLUMN_DIMS_ROWS,
		COLUMN_DIMS_COLS,
		RANK_DIMS_COLS,
		SCALAR,
		MULTI_SCALAR,
		ROW_RANK_DIMS, // right wdivmm, row mm
		COLUMN_RANK_DIMS,  // left wdivmm, row mm
		COLUMN_RANK_DIMS_T,
		VECT_CONST2;
	}
	
	private Class<?> _class = null;
	private boolean _distSupported = false;
	private int _numThreads = -1;
	private long _constDim2 = -1;
	private SpoofOutputDimsType _dimsType;
	
	public SpoofFusedOp ( ) {
	
	}
	
	public SpoofFusedOp( String name, DataType dt, ValueType vt, Class<?> cla, boolean dist, SpoofOutputDimsType type ) {
		super(name, dt, vt);
		_class = cla;
		_distSupported = dist;
		_dimsType = type;
	}

	@Override
	public void checkArity() {}

	@Override
	public void setMaxNumThreads(int k) {
		_numThreads = k;
	}

	@Override
	public int getMaxNumThreads() {
		return _numThreads;
	}

	@Override
	public boolean allowsAllExecTypes() {
		return _distSupported;
	}
	
	public void setConstDim2(long constDim2) {
		_constDim2 = constDim2;
	}

	@Override
	protected double computeOutputMemEstimate(long dim1, long dim2, long nnz) {
		return _class.getGenericSuperclass().equals(SpoofRowwise.class) ?
			OptimizerUtils.estimateSize(dim1, dim2) :
			OptimizerUtils.estimatePartitionedSizeExactSparsity(
				dim1, dim2, getRowsInBlock(), getColsInBlock(), nnz);
	}

	@Override
	protected double computeIntermediateMemEstimate(long dim1, long dim2, long nnz) {
		return 0;
	}
	
	@Override
	public Lop constructLops() {
		if( getLops() != null )
			return getLops();
		
		ExecType et = optFindExecType();
		
		ArrayList<Lop> inputs = new ArrayList<>();
		for( Hop c : getInput() )
			inputs.add(c.constructLops());
		
		int k = OptimizerUtils.getConstrainedNumThreads(_numThreads);
		SpoofFused lop = new SpoofFused(inputs, getDataType(), getValueType(), _class, k, et);
		setOutputDimensions(lop);
		setLineNumbers(lop);
		setLops(lop);
	
		return lop;
	}
	
	@Override
	protected ExecType optFindExecType() {
		
		checkAndSetForcedPlatform();
		
		if( _etypeForced != null ) {		
			_etype = _etypeForced;
		}
		else {
			_etype = findExecTypeByMemEstimate();
			checkAndSetInvalidCPDimsAndSize();
		}
		
		//ensure valid execution plans
		if( _etype == ExecType.MR )
			_etype = ExecType.CP;
		
		return _etype;
	}

	@Override
	public String getOpString() {
		return "spoof("+_class.getSimpleName()+")";
	}
	
	@Override
	protected long[] inferOutputCharacteristics( MemoTable memo )
	{
		long[] ret = null;
	
		//get statistics of main input
		MatrixCharacteristics mc = memo.getAllInputStats(getInput().get(0));
		
		if( mc.dimsKnown() ) {
			switch(_dimsType)
			{
				case ROW_DIMS:
					ret = new long[]{mc.getRows(), 1, -1};
					break;
				case COLUMN_DIMS_ROWS:
					ret = new long[]{mc.getCols(), 1, -1};
					break;
				case COLUMN_DIMS_COLS:
					ret = new long[]{1, mc.getCols(), -1};
					break;
				case RANK_DIMS_COLS: {
					MatrixCharacteristics mc2 = memo.getAllInputStats(getInput().get(1));
					if( mc2.dimsKnown() )
						ret = new long[]{1, mc2.getCols(), -1};
					break;
				}
				case INPUT_DIMS:
					ret = new long[]{mc.getRows(), mc.getCols(), -1};
					break;
				case INPUT_DIMS_CONST2:
					ret = new long[]{mc.getRows(), _constDim2, -1};
					break;
				case VECT_CONST2:
					ret = new long[]{1, _constDim2, -1};
					break;	
				case SCALAR:
					ret = new long[]{0, 0, -1};
					break;
				case MULTI_SCALAR:
					//dim2 statically set from outside
					ret = new long[]{1, _dim2, -1};
					break;
				case ROW_RANK_DIMS: {
					MatrixCharacteristics mc2 = memo.getAllInputStats(getInput().get(1));
					if( mc2.dimsKnown() )
						ret = new long[]{mc.getRows(), mc2.getCols(), -1};
					break;
				}
				case COLUMN_RANK_DIMS: {
					MatrixCharacteristics mc2 = memo.getAllInputStats(getInput().get(1));
					if( mc2.dimsKnown() )
						ret = new long[]{mc.getCols(), mc2.getCols(), -1};
					break;
				}
				case COLUMN_RANK_DIMS_T: {
					MatrixCharacteristics mc2 = memo.getAllInputStats(getInput().get(1));
					if( mc2.dimsKnown() )
						ret = new long[]{mc2.getCols(), mc.getCols(), -1};
					break;
				}
				default:
					throw new RuntimeException("Failed to infer worst-case size information "
							+ "for type: "+_dimsType.toString());
			}
		}
		
		return ret;
	}
	
	@Override
	public void refreshSizeInformation() {
		switch(_dimsType)
		{
			case ROW_DIMS:
				setDim1(getInput().get(0).getDim1());
				setDim2(1);
				break;
			case COLUMN_DIMS_ROWS:
				setDim1(getInput().get(0).getDim2());
				setDim2(1);
				break;
			case COLUMN_DIMS_COLS:
				setDim1(1);
				setDim2(getInput().get(0).getDim2());
				break;
			case RANK_DIMS_COLS:
				setDim1(1);
				setDim2(getInput().get(1).getDim2());
				break;
			case INPUT_DIMS:
				setDim1(getInput().get(0).getDim1());
				setDim2(getInput().get(0).getDim2());
				break;
			case INPUT_DIMS_CONST2:
				setDim1(getInput().get(0).getDim1());
				setDim2(_constDim2);
				break;
			case VECT_CONST2:
				setDim1(1);
				setDim2(_constDim2);
				break;
			case SCALAR:
				setDim1(0);
				setDim2(0);
				break;
			case MULTI_SCALAR:
				setDim1(1); //row vector
				//dim2 statically set from outside
				break;
			case ROW_RANK_DIMS:
				setDim1(getInput().get(0).getDim1());
				setDim2(getInput().get(1).getDim2());
				break;
			case COLUMN_RANK_DIMS:
				setDim1(getInput().get(0).getDim2());
				setDim2(getInput().get(1).getDim2());
				break;
			case COLUMN_RANK_DIMS_T:
				setDim1(getInput().get(1).getDim2());
				setDim2(getInput().get(0).getDim2());
				break;	
			default:
				throw new RuntimeException("Failed to refresh size information "
					+ "for type: "+_dimsType.toString());
		}
	}

	@Override
	public Object clone() throws CloneNotSupportedException 
	{
		SpoofFusedOp ret = new SpoofFusedOp();
		
		//copy generic attributes
		ret.clone(this, false);
		
		//copy specific attributes
		ret._class = _class;
		ret._distSupported = _distSupported;
		ret._numThreads = _numThreads;
		ret._constDim2 = _constDim2;
		ret._dimsType = _dimsType;
		return ret;
	}
	
	@Override
	public boolean compare( Hop that )
	{
		if( !(that instanceof SpoofFusedOp) )
			return false;
		
		SpoofFusedOp that2 = (SpoofFusedOp)that;
		//note: class implies dims type as well
		boolean ret = ( _class.equals(that2._class)
				&& _distSupported == that2._distSupported
				&& _numThreads == that2._numThreads
				&& _constDim2 == that2._constDim2
				&& getInput().size() == that2.getInput().size());
		
		if( ret ) {
			for( int i=0; i<getInput().size(); i++ )
				ret &= (getInput().get(i) == that2.getInput().get(i));
		}
		
		return ret;
	}

	@Override
	public boolean isGPUEnabled() {
		return false;
	}
}

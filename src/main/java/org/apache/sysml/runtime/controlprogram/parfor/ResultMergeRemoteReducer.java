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

package org.apache.sysml.runtime.controlprogram.parfor;

import java.io.IOException;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;

import org.apache.hadoop.io.NullWritable;
import org.apache.hadoop.io.Text;
import org.apache.hadoop.io.Writable;
import org.apache.hadoop.mapred.JobConf;
import org.apache.hadoop.mapred.OutputCollector;
import org.apache.hadoop.mapred.Reducer;
import org.apache.hadoop.mapred.Reporter;

import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.controlprogram.caching.MatrixObject;
import org.apache.sysml.runtime.controlprogram.parfor.stat.InfrastructureAnalyzer;
import org.apache.sysml.runtime.matrix.data.DenseBlock;
import org.apache.sysml.runtime.matrix.data.InputInfo;
import org.apache.sysml.runtime.matrix.data.MatrixBlock;
import org.apache.sysml.runtime.matrix.data.MatrixCell;
import org.apache.sysml.runtime.matrix.data.MatrixIndexes;
import org.apache.sysml.runtime.matrix.data.TaggedMatrixBlock;
import org.apache.sysml.runtime.matrix.data.TaggedMatrixCell;
import org.apache.sysml.runtime.matrix.mapred.MRJobConfiguration;
import org.apache.sysml.runtime.util.DataConverter;

/**
 * Remote result merge reducer that receives all worker results partitioned by
 * cell index or blockindex and merges all results. Due to missing resettable iterators
 * in the old mapred API we need to spill parts of the value list to disk before merging
 * in case of binaryblock.
 *
 */
public class ResultMergeRemoteReducer 
	implements Reducer<Writable, Writable, Writable, Writable>
{
	private ResultMergeReducer _reducer = null;
	
	public ResultMergeRemoteReducer( ) {
		//do nothing
	}
	
	@Override
	public void reduce(Writable key, Iterator<Writable> valueList, OutputCollector<Writable, Writable> out, Reporter reporter)
		throws IOException 
	{
		_reducer.processKeyValueList(key, valueList, out, reporter);
	}

	public void configure(JobConf job)
	{
		InputInfo ii = MRJobConfiguration.getResultMergeInputInfo(job);
		String compareFname = MRJobConfiguration.getResultMergeInfoCompareFilename(job);
		
		//determine compare required
		boolean requiresCompare = !compareFname.equals("null");
		boolean isAccum = MRJobConfiguration.getResultMergeInfoAccumulator(job);
		
		if( ii == InputInfo.TextCellInputInfo )
			_reducer = new ResultMergeReducerTextCell(requiresCompare);
		else if( ii == InputInfo.BinaryCellInputInfo )
			_reducer = new ResultMergeReducerBinaryCell(requiresCompare);
		else if( ii == InputInfo.BinaryBlockInputInfo )
			_reducer = new ResultMergeReducerBinaryBlock(requiresCompare, isAccum, job);
		else
			throw new RuntimeException("Unable to configure mapper with unknown input info: "+ii.toString()+" "+isAccum);
	}

	@Override
	public void close() throws IOException {
		//do nothing
	}

	
	private interface ResultMergeReducer //interface in order to allow ResultMergeReducerBinaryBlock to inherit from ResultMerge
	{
		void processKeyValueList( Writable key, Iterator<Writable> valueList, OutputCollector<Writable, Writable> out, Reporter reporter ) 
			throws IOException;
	}
	
	private static class ResultMergeReducerTextCell implements ResultMergeReducer
	{
		private boolean _requiresCompare;
		private StringBuilder _sb = null;
		private Text _objValue = null;
		
		public ResultMergeReducerTextCell(boolean requiresCompare) {
			_requiresCompare = requiresCompare;
			_sb = new StringBuilder();
			_objValue = new Text();
		}
		
		@Override
		public void processKeyValueList(Writable key, Iterator<Writable> valueList, OutputCollector<Writable, Writable> out, Reporter reporter)
			throws IOException 
		{
			//with compare
			if( _requiresCompare )
			{
				// NOTES MB:
				// 1) the old mapred api does not support multiple scans (reset/mark),
				//    once we switch to the new api, we can use the resetableiterator for doing
				//    the two required scans (finding the compare obj, compare all other objs)
				// 2) for 'textcell' we assume that the entire valueList fits into main memory
				//    this is valid as we group by cells, i.e., we would need millions of input files
				//    to exceed the usual 100-600MB per reduce task.
				
				//scan for compare object (incl result merge if compare available)
				MatrixIndexes key2 = (MatrixIndexes) key;
				Double cellCompare = null;
				Collection<Double> cellList = new LinkedList<>();
				boolean found = false;
				while( valueList.hasNext() ) {
					TaggedMatrixCell tVal = (TaggedMatrixCell) valueList.next();
					double lvalue = ((MatrixCell)tVal.getBaseObject()).getValue();
					if( tVal.getTag()==ResultMergeRemoteMR.COMPARE_TAG )
						cellCompare = lvalue;
					else 
					{
						if( cellCompare == null )
							cellList.add( lvalue );
						else if( cellCompare.doubleValue()!=lvalue ) //compare on the fly
						{
							_sb.append(key2.getRowIndex());
							_sb.append(' ');
							_sb.append(key2.getColumnIndex());
							_sb.append(' ');
							_sb.append(lvalue);
							_objValue.set( _sb.toString() );
							_sb.setLength(0);
							out.collect(NullWritable.get(), _objValue );
							found = true;
							break; //only one write per cell possible (independence)
						}// note: objs with equal value are directly discarded
					}
				}
				
				//result merge for objs before compare
				if( !found )
					for( Double c : cellList )
						if( !c.equals( cellCompare ) )
						{
							_sb.append(key2.getRowIndex());
							_sb.append(' ');
							_sb.append(key2.getColumnIndex());
							_sb.append(' ');
							_sb.append(c.doubleValue());
							_objValue.set( _sb.toString() );
							_sb.setLength(0);
							out.collect(NullWritable.get(), _objValue );
							break; //only one write per cell possible (independence)
						}
			}
			//without compare
			else
			{
				MatrixIndexes key2 = (MatrixIndexes) key;
				while( valueList.hasNext() )
				{
					TaggedMatrixCell tVal = (TaggedMatrixCell) valueList.next(); 
					MatrixCell value = (MatrixCell) tVal.getBaseObject();
					
					_sb.append(key2.getRowIndex());
					_sb.append(' ');
					_sb.append(key2.getColumnIndex());
					_sb.append(' ');
					_sb.append(value.getValue());
					_objValue.set( _sb.toString() );
					_sb.setLength(0);
					out.collect(NullWritable.get(), _objValue );
					break; //only one write per cell possible (independence)
				}
			}
		}
	}
	
	private static class ResultMergeReducerBinaryCell implements ResultMergeReducer
	{
		private boolean _requiresCompare;
		private MatrixCell _objValue;
		
		public ResultMergeReducerBinaryCell(boolean requiresCompare) {
			_requiresCompare = requiresCompare;
			_objValue = new MatrixCell();
		}

		@Override
		public void processKeyValueList(Writable key, Iterator<Writable> valueList, OutputCollector<Writable, Writable> out, Reporter reporter)
			throws IOException 
		{
			//with compare
			if( _requiresCompare )
			{
				// NOTES MB:
				// 1) the old mapred api does not support multiple scans (reset/mark),
				//    once we switch to the new api, we can use the resetableiterator for doing
				//    the two required scans (finding the compare obj, compare all other objs)
				// 2) for 'binarycell' we assume that the entire valueList fits into main memory
				//    this is valid as we group by cells, i.e., we would need millions of input files
				//    to exceed the usual 100-600MB per reduce task.
				
				//scan for compare object (incl result merge if compare available)
				Double cellCompare = null;
				Collection<Double> cellList = new LinkedList<>();
				boolean found = false;
				while( valueList.hasNext() ) {
					TaggedMatrixCell tVal = (TaggedMatrixCell) valueList.next();
					MatrixCell cVal = (MatrixCell) tVal.getBaseObject();
					if( tVal.getTag()==ResultMergeRemoteMR.COMPARE_TAG )
						cellCompare = cVal.getValue();
					else 
					{
						if( cellCompare == null )
							cellList.add( cVal.getValue() );
						else if( cellCompare.doubleValue() != cVal.getValue() ) //compare on the fly
						{
							out.collect(key, cVal );
							found = true;
							break; //only one write per cell possible (independence)
						}// note: objs with equal value are directly discarded
					}
				}
				
				//result merge for objs before compare
				if( !found )
					for( Double c : cellList )
						if( !c.equals( cellCompare) ) {
							_objValue.setValue(c.doubleValue());
							out.collect(key, _objValue );
							break; //only one write per cell possible (independence)
						}
			}
			//without compare
			else
			{
				while( valueList.hasNext() ) {
					TaggedMatrixCell tVal = (TaggedMatrixCell) valueList.next();
					out.collect((MatrixIndexes)key, (MatrixCell)tVal.getBaseObject());
					break; //only one write per cell possible (independence)
				}
			}
		}
	}
	
	private static class ResultMergeReducerBinaryBlock extends ResultMerge implements ResultMergeReducer
	{
		private static final long serialVersionUID = 84399890805869855L;
		
		private boolean _requiresCompare;
		private JobConf _job = null;
		
		public ResultMergeReducerBinaryBlock(boolean requiresCompare, boolean isAccum, JobConf job) {
			_requiresCompare = requiresCompare;
			_job = job;
			_isAccum = isAccum;
		}
		
		@Override
		public MatrixObject executeParallelMerge(int par) {
			throw new DMLRuntimeException("Unsupported operation.");
		}

		@Override
		public MatrixObject executeSerialMerge() {
			throw new DMLRuntimeException("Unsupported operation.");
		}

		@Override
		public void processKeyValueList(Writable key, Iterator<Writable> valueList, OutputCollector<Writable, Writable> out, Reporter reporter)
			throws IOException 
		{	
			try
			{
				MatrixIndexes ixOut = ((ResultMergeTaggedMatrixIndexes)key).getIndexes();
				MatrixBlock mbOut = null;
				DenseBlock aCompare = null;
				boolean appendOnly = false;
				
				//get and prepare compare block if required
				if( _requiresCompare ) {
					TaggedMatrixBlock tVal = (TaggedMatrixBlock) valueList.next();
					MatrixBlock bVal = (MatrixBlock) tVal.getBaseObject();
					if( tVal.getTag()!=ResultMergeRemoteMR.COMPARE_TAG )
						throw new IOException("Failed to read compare block at expected first position.");
					aCompare = DataConverter.convertToDenseBlock(bVal,
						InfrastructureAnalyzer.isLocalMode(_job));
				}
				
				//merge all result blocks into final result block 
				while( valueList.hasNext() ) {
					TaggedMatrixBlock tVal = (TaggedMatrixBlock) valueList.next();
					MatrixBlock bVal = (MatrixBlock) tVal.getBaseObject();
					if( mbOut == null ) { //copy first block
						mbOut = new MatrixBlock();
						mbOut.copy( bVal );
						appendOnly = mbOut.isInSparseFormat();
					}
					else { //merge remaining blocks
						if( _requiresCompare )
							mergeWithComp(mbOut, bVal, aCompare);
						else
							mergeWithoutComp(mbOut, bVal, appendOnly);
					}
				}
				
				//sort sparse due to append-only
				if( appendOnly && !_isAccum )
					mbOut.sortSparseRows();
				
				//change sparsity if required after 
				mbOut.examSparsity(); 
				
				out.collect(ixOut, mbOut);
			}
			catch( Exception ex )
			{
				throw new IOException(ex);
			}
		}
	}
}

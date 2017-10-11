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

package org.apache.sysml.runtime.matrix.mapred;

import java.io.DataInput;
import java.io.DataOutput;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.util.HashMap;
import java.util.Iterator;

import org.apache.hadoop.io.NullWritable;
import org.apache.hadoop.io.Text;
import org.apache.hadoop.io.Writable;
import org.apache.hadoop.mapred.JobConf;
import org.apache.hadoop.mapred.OutputCollector;
import org.apache.hadoop.mapred.Reducer;
import org.apache.hadoop.mapred.Reporter;

import org.apache.sysml.runtime.instructions.mr.CSVWriteInstruction;
import org.apache.sysml.runtime.matrix.MatrixCharacteristics;
import org.apache.sysml.runtime.matrix.data.IJV;
import org.apache.sysml.runtime.matrix.data.MatrixBlock;
import org.apache.sysml.runtime.matrix.data.TaggedFirstSecondIndexes;
import org.apache.sysml.runtime.matrix.mapred.CSVWriteReducer.RowBlockForTextOutput;
import org.apache.sysml.runtime.matrix.mapred.CSVWriteReducer.RowBlockForTextOutput.Situation;
import org.apache.sysml.runtime.util.MapReduceTool;

public class CSVWriteReducer extends ReduceBase implements Reducer<TaggedFirstSecondIndexes, MatrixBlock, NullWritable, RowBlockForTextOutput>
{
	
	private NullWritable nullKey = NullWritable.get();
	private RowBlockForTextOutput outValue = new RowBlockForTextOutput();
	private RowBlockForTextOutput zeroBlock = new RowBlockForTextOutput();
	
	private long[] rowIndexes=null;
	private long[] minRowIndexes=null;
	private long[] maxRowIndexes=null;
	private long[] colIndexes=null;
	private long[] numColBlocks=null;
	private int[] colsPerBlock=null;
	private int[] lastBlockNCols=null;
	private String[] delims=null;
	private boolean[] sparses=null;
	private int[] tagToResultIndex=null;
	
	private void addEndingMissingValues(byte tag, Reporter reporter) 
		throws IOException
	{
		long col=colIndexes[tag]+1;
		for(;col<numColBlocks[tag]; col++)
		{
			zeroBlock.setNumColumns(colsPerBlock[tag]);
			zeroBlock.setSituation(Situation.MIDDLE);
			collectFinalMultipleOutputs.directOutput(nullKey, zeroBlock, tagToResultIndex[tag], reporter);
		}
		//the last block
		if(col<=numColBlocks[tag])
		{
			zeroBlock.setNumColumns(lastBlockNCols[tag]);
			zeroBlock.setSituation(Situation.MIDDLE);
			collectFinalMultipleOutputs.directOutput(nullKey, zeroBlock, tagToResultIndex[tag], reporter);
			colIndexes[tag]=0;
		}
	}
	
	private Situation addMissingRows(byte tag, long stoppingRow, Situation sit, Reporter reporter) throws IOException
	{
		for(long row=rowIndexes[tag]+1; row<stoppingRow; row++)
		{
			for(long c=1; c<numColBlocks[tag]; c++)
			{
				zeroBlock.setNumColumns(colsPerBlock[tag]);
				zeroBlock.setSituation(sit);
				collectFinalMultipleOutputs.directOutput(nullKey, zeroBlock, tagToResultIndex[tag], reporter);
				sit=Situation.MIDDLE;
			}
			zeroBlock.setNumColumns(lastBlockNCols[tag]);
			zeroBlock.setSituation(sit);
			collectFinalMultipleOutputs.directOutput(nullKey, zeroBlock, tagToResultIndex[tag], reporter);
			colIndexes[tag]=0;
			sit=Situation.NEWLINE;
		}
		colIndexes[tag]=0;
		return sit;
	}
	
	private void addNewlineCharacter(byte tag, Reporter reporter) throws IOException 
	{
		zeroBlock.setNumColumns(0);
		zeroBlock.setSituation(Situation.NEWLINE);
		collectFinalMultipleOutputs.directOutput(nullKey, zeroBlock, tagToResultIndex[tag], reporter);
	}
	
	@Override
	public void reduce(TaggedFirstSecondIndexes inkey, Iterator<MatrixBlock> inValue,
			OutputCollector<NullWritable, RowBlockForTextOutput> out, Reporter reporter)
			throws IOException 
	{
		long begin = System.currentTimeMillis();
		
		cachedReporter = reporter;

		byte tag = inkey.getTag();
		zeroBlock.setFormatParameters(delims[tag], sparses[tag]);
		outValue.setFormatParameters(delims[tag], sparses[tag]);
		
		Situation sit = Situation.MIDDLE;
		if(rowIndexes[tag]==minRowIndexes[tag])
			sit=Situation.START;
		else if(rowIndexes[tag]!=inkey.getFirstIndex())
			sit=Situation.NEWLINE;
		
		//check whether need to fill in missing values in previous rows
		if(sit==Situation.NEWLINE)
		{
			//if the previous row has not finished
			addEndingMissingValues(tag, reporter);
		}
		
		if(sit==Situation.NEWLINE||sit==Situation.START)
		{	
			//if a row is completely missing
			sit=addMissingRows(tag, inkey.getFirstIndex(), sit, reporter);
		}
		
		//add missing value at the beginning of this row
		for(long col=colIndexes[tag]+1; col<inkey.getSecondIndex(); col++)
		{
			zeroBlock.setNumColumns(colsPerBlock[tag]);
			zeroBlock.setSituation(sit);
			collectFinalMultipleOutputs.directOutput(nullKey, zeroBlock, tagToResultIndex[tag], reporter);
			sit=Situation.MIDDLE;
		}
		
		colIndexes[tag]=inkey.getSecondIndex();
		
		while(inValue.hasNext())
		{
			MatrixBlock block = inValue.next();
			outValue.setData(block);
			outValue.setNumColumns(block.getNumColumns());
			outValue.setSituation(sit);
			
			collectFinalMultipleOutputs.directOutput(nullKey, outValue, tagToResultIndex[tag], reporter);
			resultsNonZeros[tagToResultIndex[tag]] += block.getNonZeros();
			sit = Situation.MIDDLE;
		}
		rowIndexes[tag]=inkey.getFirstIndex();

		reporter.incrCounter(Counters.COMBINE_OR_REDUCE_TIME, (System.currentTimeMillis()-begin));
	}
	
	@Override
	public void configure(JobConf job)
	{
		super.configure(job);
		byte maxIndex=0;
		HashMap<Byte, CSVWriteInstruction> out2Ins=new HashMap<>();
		try {
			CSVWriteInstruction[] ins = MRJobConfiguration.getCSVWriteInstructions(job);
			for(CSVWriteInstruction in: ins)
			{
				out2Ins.put(in.output, in);
				if(in.output>maxIndex)
					maxIndex=in.output;
			}
		} catch (Exception e) {
			throw new RuntimeException(e);
		}
		
		int numParitions=job.getNumReduceTasks();
		int taskID=MapReduceTool.getUniqueTaskId(job);
		//LOG.info("## taks id: "+taskID);
		//for efficiency only, the arrays may have missing values
		rowIndexes=new long[maxIndex+1];
		colIndexes=new long[maxIndex+1];
		maxRowIndexes=new long[maxIndex+1];
		minRowIndexes=new long[maxIndex+1];
		numColBlocks=new long[maxIndex+1];
		lastBlockNCols=new int[maxIndex+1];
		colsPerBlock=new int[maxIndex+1];
		delims=new String[maxIndex+1];
		sparses=new boolean[maxIndex+1];
		tagToResultIndex=new int[maxIndex+1];
		
		for(int i=0; i<resultIndexes.length; i++)
		{
			byte ri=resultIndexes[i];
			tagToResultIndex[ri]=i;
			CSVWriteInstruction in=out2Ins.get(ri);
			MatrixCharacteristics dim=MRJobConfiguration.getMatrixCharacteristicsForInput(job, in.input);
			delims[ri]=in.delim;
			sparses[ri]=in.sparse;
			numColBlocks[ri]=(long)Math.ceil((double)dim.getCols()/(double) dim.getColsPerBlock());
			lastBlockNCols[ri]=(int) (dim.getCols()%dim.getColsPerBlock());
			colsPerBlock[ri]=dim.getColsPerBlock();
			long rstep=(long)Math.ceil((double)dim.getRows()/(double)numParitions);
			minRowIndexes[ri]=rowIndexes[ri]=rstep*taskID;
			maxRowIndexes[ri]=Math.min(rstep*(taskID+1), dim.getRows());
			colIndexes[ri]=0;
		}
		
		zeroBlock.setData(new MatrixBlock());
	}
	
	@Override
	public void close() throws IOException
	{
		for( byte tag : resultIndexes )
		{
			//if the previous row has not finished
			addEndingMissingValues(tag, cachedReporter);
			
			//if a row is completely missing
			addMissingRows(tag, maxRowIndexes[tag]+1, Situation.NEWLINE, cachedReporter); 
			
			// add a newline character at the end of file
			addNewlineCharacter(tag, cachedReporter);
		}
		
		super.close();
	}

	
	/**
	 * Custom output writable to prevent automatic newline after each partial block.
	 * Writing partial blocks is important for robustness in case of very large rows
	 * (otherwise there would be potential to run OOM).
	 * 
	 */
	public static class RowBlockForTextOutput implements Writable
	{
		public static enum Situation{
			START, 
			NEWLINE, 
			MIDDLE
		}
		
		private MatrixBlock _data = null;
		private int _numCols = 0;
		private Situation _sit = Situation.START;
		
		private String delim=",";
		private boolean sparse=true;
		
		private StringBuilder _buffer = new StringBuilder();
		
		
		public RowBlockForTextOutput()
		{
			
		}
		
		public void setData(MatrixBlock block)
		{
			_data = block;
		}
		
		public void setNumColumns(int cols)
		{
			_numCols = cols;
		}
		
		public void setSituation(Situation s)
		{
			_sit = s;
		}
		
		public void setFormatParameters(String del, boolean sps)
		{
			delim=del;
			sparse=sps;
		}
		
		@Override
		public void readFields(DataInput arg0) throws IOException {
			throw new IOException("this is not supposed to be called!");
		}

		@Override
		public void write(DataOutput out) 
			throws IOException 
		{
			_buffer.setLength(0);
			switch( _sit )
			{
				case START:
					break;
				case NEWLINE:
					_buffer.append('\n');
					break;
				case MIDDLE:
					_buffer.append(delim);
					break;
				default:
					throw new RuntimeException("Unrecognized situation "+_sit);	
			}
			
			//serialize data if required (not newline)
			if ( _numCols > 0 ) 
			{
				if( _data.isEmptyBlock(false) ) //EMPTY BLOCK
				{
					appendZero(_buffer, sparse, delim, false, _numCols);
				}
				else if( _data.isInSparseFormat() ) //SPARSE BLOCK
				{
					Iterator<IJV> iter = _data.getSparseBlockIterator();
					int j = -1;
					while( iter.hasNext() )
					{
						IJV cell = iter.next();
						appendZero(_buffer, sparse, delim, true, cell.getJ()-j-1);
						
						j = cell.getJ(); //current col
						if( cell.getV() != 0 ) //for nnz
							_buffer.append(cell.getV());
						else if( !sparse ) 
							_buffer.append('0');
						if( j < _numCols-1 )
							_buffer.append(delim);
					}
					appendZero(_buffer, sparse, delim, false, _numCols-j-1);
				}
				else //DENSE BLOCK
				{
					for(int j=0; j<_numCols; j++)
					{
						double val = _data.getValueDenseUnsafe(0, j);
						if( val!=0 ) //for nnz
							_buffer.append(val);
						else if( !sparse ) 
							_buffer.append('0');
							
						if( j < _numCols-1 )
							_buffer.append(delim);
					}	
				}
			}
			
			ByteBuffer bytes = Text.encode(_buffer.toString());
			int length = bytes.limit();
		    out.write(bytes.array(), 0, length);
		}

		private static void appendZero( StringBuilder buffer, boolean sparse, String delim, boolean alwaysDelim, int len )
		{
			if( len <= 0 )
				return;
			
			for( int i=0; i<len; i++ )
			{
				if( !sparse ) //single character
					buffer.append('0');
				if( alwaysDelim || i < len-1 )
					buffer.append(delim);
			}
		}		
	}
}

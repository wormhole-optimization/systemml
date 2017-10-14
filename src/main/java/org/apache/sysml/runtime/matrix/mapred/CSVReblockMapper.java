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

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;

import org.apache.hadoop.fs.FileSystem;
import org.apache.hadoop.fs.Path;
import org.apache.hadoop.io.ByteWritable;
import org.apache.hadoop.io.LongWritable;
import org.apache.hadoop.io.SequenceFile;
import org.apache.hadoop.io.Text;
import org.apache.hadoop.io.Writable;
import org.apache.hadoop.mapred.JobConf;
import org.apache.hadoop.mapred.Mapper;
import org.apache.hadoop.mapred.OutputCollector;
import org.apache.hadoop.mapred.Reporter;
import org.apache.sysml.runtime.instructions.mr.CSVReblockInstruction;
import org.apache.sysml.runtime.io.IOUtilFunctions;
import org.apache.sysml.runtime.matrix.CSVReblockMR;
import org.apache.sysml.runtime.matrix.CSVReblockMR.BlockRow;
import org.apache.sysml.runtime.matrix.CSVReblockMR.OffsetCount;
import org.apache.sysml.runtime.matrix.data.MatrixBlock;
import org.apache.sysml.runtime.matrix.data.TaggedFirstSecondIndexes;
import org.apache.sysml.runtime.util.UtilFunctions;

public class CSVReblockMapper extends MapperBase implements Mapper<LongWritable, Text, TaggedFirstSecondIndexes, BlockRow>
{
	private long rowOffset=0;
	private boolean first=true;
	private long num=0;
	private HashMap<Long, Long> offsetMap=new HashMap<>();
	private String _delim=" ";
	private boolean ignoreFirstLine=false;
	private boolean headerFile=false;

	private IndexedBlockRow idxRow = null;
	
	public static class IndexedBlockRow 
	{
		private BlockRow row=null;
		private TaggedFirstSecondIndexes outIndexes=null;
		
		public IndexedBlockRow() {
			row = new BlockRow();
			row.data = new MatrixBlock();
			outIndexes=new TaggedFirstSecondIndexes();
		}
		
		public BlockRow getRow() { return row; }
		public TaggedFirstSecondIndexes getIndexes() { return outIndexes; }
	}
	
	
	public static IndexedBlockRow processRow(IndexedBlockRow row, String[] cells, long rowOffset, long num, byte outTag, int brlen, int bclen, boolean fill, double fillValue, OutputCollector<TaggedFirstSecondIndexes, BlockRow> out) throws IOException
	{
		int start=0;
		row.getIndexes().setTag(outTag);
		long rowIndex=UtilFunctions.computeBlockIndex(rowOffset+num+1, brlen);
		row.getRow().indexInBlock=UtilFunctions.computeCellInBlock(rowOffset+num+1, brlen);
		
		long col=0;
		for(; col<cells.length/bclen; col++)
		{
			row.getRow().data.reset(1, bclen);
			row.getIndexes().setIndexes(rowIndex, col+1);
			for(int k=0;k<bclen; k++)
			{
				if(cells[k+start] == null || cells[k+start].isEmpty())
				{
					IOUtilFunctions.checkAndRaiseErrorCSVEmptyField(null, fill, true);
					row.getRow().data.appendValue(0, k, fillValue);
				}
				else
					row.getRow().data.appendValue(0, k, UtilFunctions.parseToDouble(cells[k+start]));
			}
			out.collect(row.getIndexes(), row.getRow());
			start+=bclen;
		}
		row.getIndexes().setIndexes(rowIndex, col+1);
		int lastBclen=cells.length%bclen;
		if(lastBclen!=0)
		{
			row.getRow().data.reset(1, lastBclen);
			for(int k=0;k<lastBclen; k++)
			{
				if(cells[k+start] == null || cells[k+start].isEmpty())
				{
					if(!fill)
						throw new RuntimeException("Empty fields found in the input delimited file. Use \"fill\" option to read delimited files with empty fields.");
					row.getRow().data.appendValue(0, k, fillValue);
				}
				else
					row.getRow().data.appendValue(0, k, UtilFunctions.parseToDouble(cells[k+start]));
			}
			out.collect(row.getIndexes(), row.getRow());
		}
		return row;
	}
	
	@Override
	public void map(LongWritable key, Text value,
			OutputCollector<TaggedFirstSecondIndexes, BlockRow> out, Reporter reporter)
			throws IOException 
	{
		if(first) {
			rowOffset=offsetMap.get(key.get());
			first=false;
		}
		
		if(key.get()==0 && headerFile && ignoreFirstLine)
			return;
		
		String[] cells = IOUtilFunctions.split( value.toString(), _delim );
		
		for(int i=0; i<representativeMatrixes.size(); i++)
			for(CSVReblockInstruction ins: csv_reblock_instructions.get(i))
			{
				idxRow = processRow(idxRow, cells, rowOffset, num, ins.output, ins.brlen, ins.bclen, ins.fill, ins.fillValue, out);
			}
		
		num++;
	}	
	
	@Override
	@SuppressWarnings("deprecation")
	public void configure(JobConf job)
	{
		super.configure(job);
		//get the number colums per block
		
		//load the offset mapping
		byte matrixIndex=representativeMatrixes.get(0);
		try 
		{
			Path thisPath=new Path(job.get(MRConfigurationNames.MR_MAP_INPUT_FILE));
			FileSystem fs = IOUtilFunctions.getFileSystem(thisPath, job);
			thisPath = thisPath.makeQualified(fs);
			String filename=thisPath.toString();
			Path headerPath=new Path(job.getStrings(CSVReblockMR.SMALLEST_FILE_NAME_PER_INPUT)[matrixIndex]).makeQualified(fs);
			if(headerPath.toString().equals(filename))
				headerFile=true;
			
			ByteWritable key=new ByteWritable();
			OffsetCount value=new OffsetCount();
			Path p=new Path(job.get(CSVReblockMR.ROWID_FILE_NAME));
			SequenceFile.Reader reader = null;
			try {
				reader = new SequenceFile.Reader(fs, p, job);
				while (reader.next(key, value)) {
					if(key.get()==matrixIndex && filename.equals(value.filename))
						offsetMap.put(value.fileOffset, value.count);
				}
			}
			finally {
				IOUtilFunctions.closeSilently(reader);
			}
		} 
		catch (IOException e) {
			throw new RuntimeException(e);
		}
		
		CSVReblockInstruction ins=csv_reblock_instructions.get(0).get(0);
		_delim = ins.delim;
		ignoreFirstLine=ins.hasHeader;
		
		idxRow = new IndexedBlockRow();
		int maxBclen=0;
	
		for(ArrayList<CSVReblockInstruction> insv: csv_reblock_instructions)
			for(CSVReblockInstruction in: insv)
			{	
				if(maxBclen<in.bclen)
					maxBclen=in.bclen;
			}
		
		//always dense since common csv usecase
		idxRow.getRow().data.reset(1, maxBclen, false);		
	}

	@Override
	protected void specialOperationsForActualMap(int index,
			OutputCollector<Writable, Writable> out, Reporter reporter)
		throws IOException 
	{
		//do nothing
	}	
}

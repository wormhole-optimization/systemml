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

package org.apache.sysml.runtime.io;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

import org.apache.hadoop.fs.FileSystem;
import org.apache.hadoop.fs.Path;
import org.apache.hadoop.io.LongWritable;
import org.apache.hadoop.io.Text;
import org.apache.hadoop.mapred.FileInputFormat;
import org.apache.hadoop.mapred.InputSplit;
import org.apache.hadoop.mapred.JobConf;
import org.apache.hadoop.mapred.RecordReader;
import org.apache.hadoop.mapred.Reporter;
import org.apache.hadoop.mapred.TextInputFormat;

import org.apache.sysml.conf.ConfigurationManager;
import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.matrix.data.DenseBlock;
import org.apache.sysml.runtime.matrix.data.InputInfo;
import org.apache.sysml.runtime.matrix.data.MatrixBlock;
import org.apache.sysml.runtime.util.FastStringTokenizer;
import org.apache.sysml.runtime.util.MapReduceTool;

public class ReaderTextCell extends MatrixReader
{
	private boolean _isMMFile = false;
	
	public ReaderTextCell(InputInfo info)
	{
		_isMMFile = (info == InputInfo.MatrixMarketInputInfo);
	}
	
	@Override
	public MatrixBlock readMatrixFromHDFS(String fname, long rlen, long clen, int brlen, int bclen, long estnnz) 
		throws IOException, DMLRuntimeException 
	{
		//prepare file access
		JobConf job = new JobConf(ConfigurationManager.getCachedJobConf());
		Path path = new Path( fname );
		FileSystem fs = IOUtilFunctions.getFileSystem(path, job);
		
		//allocate output matrix block
		if( estnnz < 0 )
			estnnz = MapReduceTool.estimateNnzBasedOnFileSize(path, rlen, clen, brlen, bclen, 3);
		MatrixBlock ret = createOutputMatrixBlock(rlen, clen, (int)rlen, (int)clen, estnnz, true, false);
		
		//check existence and non-empty file
		checkValidInputFile(fs, path); 
	
		//core read 
		if( fs.isDirectory(path) )
			readTextCellMatrixFromHDFS(path, job, ret, rlen, clen, brlen, bclen);
		else
			readRawTextCellMatrixFromHDFS(path, job, fs, ret, rlen, clen, brlen, bclen, _isMMFile);
		
		//finally check if change of sparse/dense block representation required
		if( !ret.isInSparseFormat() )
			ret.recomputeNonZeros();
		ret.examSparsity();
		
		return ret;
	}

	@Override
	public MatrixBlock readMatrixFromInputStream(InputStream is, long rlen, long clen, int brlen, int bclen, long estnnz) 
		throws IOException, DMLRuntimeException 
	{
		//allocate output matrix block
		MatrixBlock ret = createOutputMatrixBlock(rlen, clen, brlen, bclen, estnnz, true, false);
	
		//core read 
		readRawTextCellMatrixFromInputStream(is, ret, rlen, clen, brlen, bclen, _isMMFile);
		
		//finally check if change of sparse/dense block representation required
		if( !ret.isInSparseFormat() )
			ret.recomputeNonZeros();
		ret.examSparsity();
		
		return ret;
	}

	private static void readTextCellMatrixFromHDFS( Path path, JobConf job, MatrixBlock dest, long rlen, long clen, int brlen, int bclen )
		throws IOException
	{
		boolean sparse = dest.isInSparseFormat();
		FileInputFormat.addInputPath(job, path);
		TextInputFormat informat = new TextInputFormat();
		informat.configure(job);
		InputSplit[] splits = informat.getSplits(job, 1);
		
		LongWritable key = new LongWritable();
		Text value = new Text();
		int row = -1;
		int col = -1;
		
		try
		{
			FastStringTokenizer st = new FastStringTokenizer(' ');
			
			for(InputSplit split: splits)
			{
				RecordReader<LongWritable,Text> reader = informat.getRecordReader(split, job, Reporter.NULL);
			
				try
				{
					if( sparse ) //SPARSE<-value
					{
						while( reader.next(key, value) ) {
							st.reset( value.toString() ); //reinit tokenizer
							row = st.nextInt() - 1;
							col = st.nextInt() - 1;
							if(row == -1 || col == -1) continue;
							double lvalue = st.nextDouble();
							dest.appendValue(row, col, lvalue);
						}
						
						dest.sortSparseRows();
					} 
					else //DENSE<-value
					{
						DenseBlock a = dest.getDenseBlock();
						while( reader.next(key, value) ) {
							st.reset( value.toString() ); //reinit tokenizer
							row = st.nextInt()-1;
							col = st.nextInt()-1;
							if(row == -1 || col == -1) continue;
							double lvalue = st.nextDouble();
							a.set( row, col, lvalue );
						}
					}
				}
				finally {
					IOUtilFunctions.closeSilently(reader);
				}
			}
		}
		catch(Exception ex) {
			//post-mortem error handling and bounds checking
			if( row < 0 || row + 1 > rlen || col < 0 || col + 1 > clen )
				throw new IOException("Matrix cell ["+(row+1)+","+(col+1)+"] " +
									  "out of overall matrix range [1:"+rlen+",1:"+clen+"].");
			else
				throw new IOException( "Unable to read matrix in text cell format.", ex );
		}
	}

	private static void readRawTextCellMatrixFromHDFS( Path path, JobConf job, FileSystem fs, MatrixBlock dest, long rlen, long clen, int brlen, int bclen, boolean matrixMarket )
		throws IOException
	{
		//create input stream for path
		InputStream inputStream = fs.open(path);
		
		//actual read
		readRawTextCellMatrixFromInputStream(inputStream, dest, rlen, clen, brlen, bclen, matrixMarket);
	}

	private static void readRawTextCellMatrixFromInputStream( InputStream is, MatrixBlock dest, long rlen, long clen, int brlen, int bclen, boolean matrixMarket )
			throws IOException
	{
		BufferedReader br = new BufferedReader(new InputStreamReader( is ));
		
		boolean sparse = dest.isInSparseFormat();
		String value = null;
		int row = -1;
		int col = -1;
		
		// Read the header lines, if reading from a matrixMarket file
		if ( matrixMarket ) {
			value = br.readLine(); // header line
			if ( value==null || !value.startsWith("%%") ) {
				throw new IOException("Error while reading file in MatrixMarket format. Expecting a header line, but encountered, \"" + value +"\".");
			}
			
			// skip until end-of-comments
			while( (value = br.readLine())!=null && value.charAt(0) == '%' ) {
				//do nothing just skip comments
			}
			
			// the first line after comments is the one w/ matrix dimensions
			// validate (rlen clen nnz)
			String[] fields = value.trim().split("\\s+"); 
			long mm_rlen = Long.parseLong(fields[0]);
			long mm_clen = Long.parseLong(fields[1]);
			if ( rlen != mm_rlen || clen != mm_clen ) {
				throw new IOException("Unexpected matrix dimensions while reading file in MatrixMarket format. Expecting dimensions [" + rlen + " rows, " + clen + " cols] but encountered [" + mm_rlen + " rows, " + mm_clen + "cols].");
			}
		}
		
		try
		{			
			FastStringTokenizer st = new FastStringTokenizer(' ');
			
			if( sparse ) //SPARSE<-value
			{
				while( (value=br.readLine())!=null )
				{
					st.reset( value ); //reinit tokenizer
					row = st.nextInt()-1;
					col = st.nextInt()-1;
					if(row == -1 || col == -1) continue;
					double lvalue = st.nextDouble();
					dest.appendValue(row, col, lvalue);
				}
				
				dest.sortSparseRows();
			} 
			else //DENSE<-value
			{
				DenseBlock a = dest.getDenseBlock();
				while( (value=br.readLine())!=null ) {
					st.reset( value ); //reinit tokenizer
					row = st.nextInt()-1;
					col = st.nextInt()-1;
					if(row == -1 || col == -1) continue;
					double lvalue = st.nextDouble();
					a.set( row, col, lvalue );
				}
			}
		}
		catch(Exception ex) {
			//post-mortem error handling and bounds checking
			if( row < 0 || row + 1 > rlen || col < 0 || col + 1 > clen ) 
				throw new IOException("Matrix cell ["+(row+1)+","+(col+1)+"] " +
									  "out of overall matrix range [1:"+rlen+",1:"+clen+"].", ex);
			else
				throw new IOException( "Unable to read matrix in raw text cell format.", ex );
		}
		finally {
			IOUtilFunctions.closeSilently(br);
		}
	}
}

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

package org.apache.sysml.runtime.instructions.cpfile;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map.Entry;

import org.apache.hadoop.fs.FileSystem;
import org.apache.hadoop.fs.Path;
import org.apache.hadoop.io.LongWritable;
import org.apache.hadoop.io.SequenceFile;
import org.apache.hadoop.io.Text;
import org.apache.hadoop.mapred.FileInputFormat;
import org.apache.hadoop.mapred.InputSplit;
import org.apache.hadoop.mapred.JobConf;
import org.apache.hadoop.mapred.RecordReader;
import org.apache.hadoop.mapred.Reporter;
import org.apache.hadoop.mapred.TextInputFormat;
import org.apache.sysml.conf.ConfigurationManager;
import org.apache.sysml.parser.Expression.DataType;
import org.apache.sysml.parser.Expression.ValueType;
import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.controlprogram.caching.CacheException;
import org.apache.sysml.runtime.controlprogram.caching.MatrixObject;
import org.apache.sysml.runtime.controlprogram.context.ExecutionContext;
import org.apache.sysml.runtime.controlprogram.parfor.util.Cell;
import org.apache.sysml.runtime.controlprogram.parfor.util.IDHandler;
import org.apache.sysml.runtime.controlprogram.parfor.util.StagingFileUtils;
import org.apache.sysml.runtime.functionobjects.ParameterizedBuiltin;
import org.apache.sysml.runtime.functionobjects.ValueFunction;
import org.apache.sysml.runtime.instructions.InstructionUtils;
import org.apache.sysml.runtime.instructions.cp.CPOperand;
import org.apache.sysml.runtime.instructions.cp.ParameterizedBuiltinCPInstruction;
import org.apache.sysml.runtime.io.IOUtilFunctions;
import org.apache.sysml.runtime.io.MatrixWriter;
import org.apache.sysml.runtime.matrix.MatrixCharacteristics;
import org.apache.sysml.runtime.matrix.MatrixFormatMetaData;
import org.apache.sysml.runtime.matrix.data.InputInfo;
import org.apache.sysml.runtime.matrix.data.MatrixBlock;
import org.apache.sysml.runtime.matrix.data.MatrixCell;
import org.apache.sysml.runtime.matrix.data.MatrixIndexes;
import org.apache.sysml.runtime.matrix.data.OutputInfo;
import org.apache.sysml.runtime.matrix.operators.Operator;
import org.apache.sysml.runtime.matrix.operators.SimpleOperator;
import org.apache.sysml.runtime.util.FastStringTokenizer;
import org.apache.sysml.runtime.util.LocalFileUtils;
import org.apache.sysml.runtime.util.MapReduceTool;

/**
 * File-based (out-of-core) realization of remove empty for robustness because there is no
 * parallel version due to data-dependent row- and column dependencies.
 * 
 */
public class ParameterizedBuiltinCPFileInstruction extends ParameterizedBuiltinCPInstruction {

	private ParameterizedBuiltinCPFileInstruction(Operator op, HashMap<String, String> paramsMap, CPOperand out,
			String opcode, String istr) {
		super(op, paramsMap, out, opcode, istr);
	}

	public static ParameterizedBuiltinCPFileInstruction parseInstruction( String str ) 
		throws DMLRuntimeException 
	{
		String[] parts = InstructionUtils.getInstructionPartsWithValueType(str);
		// first part is always the opcode
		String opcode = parts[0];
		// last part is always the output
		CPOperand out = new CPOperand( parts[parts.length-1] ); 

		// process remaining parts and build a hash map
		HashMap<String,String> paramsMap = constructParameterMap(parts);

		// determine the appropriate value function
		ValueFunction func = null;
		if ( opcode.equalsIgnoreCase("rmempty") ) {
			func = ParameterizedBuiltin.getParameterizedBuiltinFnObject(opcode);
			return new ParameterizedBuiltinCPFileInstruction(new SimpleOperator(func), paramsMap, out, opcode, str);
		}
		else {
			throw new DMLRuntimeException("Unknown opcode (" + opcode + ") for ParameterizedBuiltin Instruction.");
		}
	}
	
	@Override 
	public void processInstruction(ExecutionContext ec) 
		throws DMLRuntimeException 
	{
		String opcode = getOpcode();
		
		if ( opcode.equalsIgnoreCase("rmempty") ) 
		{
			// get inputs
			MatrixObject src = ec.getMatrixObject( params.get("target") );
			MatrixObject out = ec.getMatrixObject( output.getName() );
			String margin = params.get("margin");
			
			// export input matrix (if necessary)
			src.exportData();
			
			//core execution
			RemoveEmpty rm = new RemoveEmpty( margin, src, out );
			out = rm.execute();
		
			//put output
			ec.setVariable(output.getName(), out);
		}
		else {
			throw new DMLRuntimeException("Unknown opcode : " + opcode);
		}
	}

	/**
	 * Remove empty rows as a inner class in order to allow testing independent of the
	 * overall SystemML instruction framework.
	 * 
	 */
	public static class RemoveEmpty
	{
		private String _margin = null;
		private MatrixObject _src = null;
		private MatrixObject _out = null;
		
		public RemoveEmpty( String margin, MatrixObject src, MatrixObject out )
		{
			_margin = margin;
			_src = src;
			_out = out;
		}

		public MatrixObject execute() 
			throws DMLRuntimeException 
		{
			//Timing time = new Timing();
			//time.start();
			
			//initial setup
			String fnameOld = _src.getFileName();
			String fnameNew = _out.getFileName();
			InputInfo ii = ((MatrixFormatMetaData)_src.getMetaData()).getInputInfo();
			MatrixCharacteristics mc = _src.getMatrixCharacteristics();
			
			String stagingDir = LocalFileUtils.getUniqueWorkingDir(LocalFileUtils.CATEGORY_WORK);
			LocalFileUtils.createLocalFileIfNotExist(stagingDir);
			
			long ret = -1;
			try
			{
				boolean diagBlocks = false;
				
				//Phase 1: write file to staging 
				if( ii == InputInfo.TextCellInputInfo )
					createTextCellStagingFile( fnameOld, stagingDir );
				else if( ii == InputInfo.BinaryCellInputInfo )
					createBinaryCellStagingFile( fnameOld, stagingDir );
				else if( ii == InputInfo.BinaryBlockInputInfo )
					diagBlocks = createBinaryBlockStagingFile( fnameOld, stagingDir );
				
				//System.out.println("Executed phase 1 in "+time.stop());
				
				//Phase 2: scan empty rows/cols
				if( diagBlocks )
					ret = createKeyMappingDiag(stagingDir, mc.getRows(), mc.getCols(), mc.getRowsPerBlock(), mc.getColsPerBlock(), ii);
				else
					ret = createKeyMapping(stagingDir, mc.getRows(), mc.getCols(), mc.getRowsPerBlock(), mc.getColsPerBlock(), ii);
				
				//System.out.println("Executed phase 2 in "+time.stop());
				
				//Phase 3: create output files
				MapReduceTool.deleteFileIfExistOnHDFS(fnameNew);
				if(   ii == InputInfo.TextCellInputInfo 
				   || ii == InputInfo.BinaryCellInputInfo )
				{
					createCellResultFile( fnameNew, stagingDir, mc.getRows(), mc.getCols(), mc.getRowsPerBlock(), mc.getColsPerBlock(), ii );
				}
				else if( ii == InputInfo.BinaryBlockInputInfo )
				{
					if( diagBlocks )
						createBlockResultFileDiag( fnameNew, stagingDir, mc.getRows(), mc.getCols(), ret, mc.getNonZeros(), mc.getRowsPerBlock(), mc.getColsPerBlock(), ii );
					else
						createBlockResultFile( fnameNew, stagingDir, mc.getRows(), mc.getCols(), ret, mc.getNonZeros(), mc.getRowsPerBlock(), mc.getColsPerBlock(), ii );
				}
				
				//System.out.println("Executed phase 3 in "+time.stop());
			}
			catch( IOException ioe )
			{
				throw new DMLRuntimeException( ioe );
			}
			
			//final cleanup
			LocalFileUtils.cleanupWorkingDirectory(stagingDir);
			
			//create and return new output object
			if( _margin.equals("rows") )
				return createNewOutputObject(_src, _out, ret, mc.getCols());
			else
				return createNewOutputObject(_src, _out, mc.getRows(), ret );
		}

		private MatrixObject createNewOutputObject( MatrixObject src, MatrixObject out, long rows, long cols ) 
			throws DMLRuntimeException
		{
			String varName = out.getVarName();
			String fName = out.getFileName();
			ValueType vt = src.getValueType();
			MatrixFormatMetaData metadata = (MatrixFormatMetaData) src.getMetaData();
			
			MatrixObject moNew = new MatrixObject( vt, fName );
			moNew.setVarName( varName );
			moNew.setDataType( DataType.MATRIX );
			
			//handle empty output block (ensure valid dimensions)
			if( rows==0 || cols ==0 ){
				rows = Math.max(rows, 1);
				cols = Math.max(cols, 1);
				try {
					moNew.acquireModify(new MatrixBlock((int)rows, (int) cols, true));
					moNew.release();
				} 
				catch (CacheException e) {
					throw new DMLRuntimeException(e);
				}
			}
			
			//create deep copy of metadata obj
			MatrixCharacteristics mcOld = metadata.getMatrixCharacteristics();
			OutputInfo oiOld = metadata.getOutputInfo();
			InputInfo iiOld = metadata.getInputInfo();
			MatrixCharacteristics mc = new MatrixCharacteristics( rows, cols, mcOld.getRowsPerBlock(),
					                                              mcOld.getColsPerBlock(), mcOld.getNonZeros());
			MatrixFormatMetaData meta = new MatrixFormatMetaData(mc,oiOld,iiOld);
			moNew.setMetaData( meta );

			return moNew;
		}

		public void createTextCellStagingFile( String fnameOld, String stagingDir ) 
			throws IOException, DMLRuntimeException
		{	
			//prepare input
			JobConf job = new JobConf(ConfigurationManager.getCachedJobConf());	
			Path path = new Path(fnameOld);
			FileSystem fs = IOUtilFunctions.getFileSystem(path, job);
			if( !fs.exists(path) )	
				throw new IOException("File "+fnameOld+" does not exist on HDFS.");
			FileInputFormat.addInputPath(job, path); 
			TextInputFormat informat = new TextInputFormat();
			informat.configure(job);
			InputSplit[] splits = informat.getSplits(job, 1);
		
			LinkedList<Cell> buffer = new LinkedList<Cell>();
			
			LongWritable key = new LongWritable();
			Text value = new Text();
			FastStringTokenizer st = new FastStringTokenizer(' ');		
			
			for(InputSplit split: splits)
			{
				RecordReader<LongWritable,Text> reader = informat.getRecordReader(split, job, Reporter.NULL);				
				try
				{
					while( reader.next(key, value) )
					{
						st.reset( value.toString() ); //reset tokenizer
						long row = st.nextLong();
						long col = st.nextLong();
						double lvalue = st.nextDouble();
						
						buffer.add(new Cell(row,col,lvalue));
						
						if( buffer.size() > StagingFileUtils.CELL_BUFFER_SIZE )
						{
							appendCellBufferToStagingArea(stagingDir, buffer, ConfigurationManager.getBlocksize(), ConfigurationManager.getBlocksize());
							buffer.clear();
						}
					}
					
					if( !buffer.isEmpty() )
					{
						appendCellBufferToStagingArea(stagingDir, buffer, ConfigurationManager.getBlocksize(), ConfigurationManager.getBlocksize());
						buffer.clear();
					}
				}
				finally {
					IOUtilFunctions.closeSilently(reader);
				}
			}
		}		

		@SuppressWarnings("deprecation")
		public void createBinaryCellStagingFile( String fnameOld, String stagingDir ) 
			throws IOException, DMLRuntimeException
		{
			//prepare input
			JobConf job = new JobConf(ConfigurationManager.getCachedJobConf());	
			Path path = new Path(fnameOld);
			FileSystem fs = IOUtilFunctions.getFileSystem(path, job);
			if( !fs.exists(path) )	
				throw new IOException("File "+fnameOld+" does not exist on HDFS.");
			
			LinkedList<Cell> buffer = new LinkedList<Cell>();
			
			MatrixIndexes key = new MatrixIndexes();
			MatrixCell value = new MatrixCell();

			for(Path lpath: IOUtilFunctions.getSequenceFilePaths(fs, path))
			{
				SequenceFile.Reader reader = new SequenceFile.Reader(fs,lpath,job);
				try
				{
					while(reader.next(key, value))
					{
						long row = key.getRowIndex();
						long col = key.getColumnIndex();
						double lvalue = value.getValue();
						
						buffer.add(new Cell(row,col,lvalue));
						
						if( buffer.size() > StagingFileUtils.CELL_BUFFER_SIZE )
						{
							appendCellBufferToStagingArea(stagingDir, buffer, ConfigurationManager.getBlocksize(), ConfigurationManager.getBlocksize());
							buffer.clear();
						}
					}
					
					if( !buffer.isEmpty() )
					{
						appendCellBufferToStagingArea(stagingDir, buffer, ConfigurationManager.getBlocksize(), ConfigurationManager.getBlocksize());
						buffer.clear();
					}
				}
				finally {
					IOUtilFunctions.closeSilently(reader);
				}
			}
		}

		/**
		 * Creates a binary block staging file and returns if the input matrix is a diag,
		 * because diag is the primary usecase and there is lots of optimization potential.
		 * 
		 * @param fnameOld old filename
		 * @param stagingDir staging directory
		 * @return true if diag
		 * @throws IOException if IOException occurs
		 * @throws DMLRuntimeException if DMLRuntimeException occurs
		 */
		@SuppressWarnings("deprecation")
		public boolean createBinaryBlockStagingFile( String fnameOld, String stagingDir ) 
			throws IOException, DMLRuntimeException
		{
			//prepare input
			JobConf job = new JobConf(ConfigurationManager.getCachedJobConf());	
			Path path = new Path(fnameOld);
			FileSystem fs = IOUtilFunctions.getFileSystem(path, job);
			if( !fs.exists(path) )	
				throw new IOException("File "+fnameOld+" does not exist on HDFS.");
			
			MatrixIndexes key = new MatrixIndexes(); 
			MatrixBlock value = new MatrixBlock();
			boolean diagBlocks = true;
			
			for(Path lpath : IOUtilFunctions.getSequenceFilePaths(fs, path))
			{
				SequenceFile.Reader reader = new SequenceFile.Reader(fs,lpath,job);
				
				try
				{
					while( reader.next(key, value) )
					{
						if( !value.isEmptyBlock() ) //skip empty blocks (important for diag)
						{
							String fname = stagingDir +"/"+key.getRowIndex()+"_"+key.getColumnIndex();
							LocalFileUtils.writeMatrixBlockToLocal(fname, value);							
							diagBlocks &= (key.getRowIndex()==key.getColumnIndex());
						}
					}	
				}
				finally {
					IOUtilFunctions.closeSilently(reader);
				}
			}
			
			return diagBlocks;
		}

		private void appendCellBufferToStagingArea( String dir, LinkedList<Cell> buffer, int brlen, int bclen ) 
			throws DMLRuntimeException, IOException
		{
			HashMap<String,LinkedList<Cell>> sortedBuffer = new HashMap<String,LinkedList<Cell>>();
			
			//sort cells in buffer wrt key
			String key = null;
			for( Cell c : buffer )
			{
				key = (c.getRow()/brlen+1) +"_"+(c.getCol()/bclen+1);
				
				if( !sortedBuffer.containsKey(key) )
					sortedBuffer.put(key, new LinkedList<Cell>());
				sortedBuffer.get(key).addLast(c);
			}	
			
			//write lists of cells to local files
			for( Entry<String,LinkedList<Cell>> e : sortedBuffer.entrySet() )
			{
				
				String pfname = dir + "/" + e.getKey();
				StagingFileUtils.writeCellListToLocal(pfname, e.getValue());
			}
		}	

		private long createKeyMapping( String stagingDir, long rlen, long clen, int brlen, int bclen, InputInfo ii) 
			throws FileNotFoundException, IOException, DMLRuntimeException 
		{
			String metaOut = stagingDir+"/meta";
			
			long len = 0;
			long lastKey = 0;
			
			if(_margin.equals("rows"))
			{
				for(int blockRow = 0; blockRow < (int)Math.ceil(rlen/(double)brlen); blockRow++)
				{	
					boolean[] flags = new boolean[brlen];
					for( int k=0; k<brlen; k++ )
						flags[k] = true;
					
					//scan for empty rows
					for(int blockCol = 0; blockCol < (int)Math.ceil(clen/(double)bclen); blockCol++)
					{
						String fname = stagingDir+"/"+(blockRow+1)+"_"+(blockCol+1);
						if( ii == InputInfo.BinaryBlockInputInfo ){
							if( !LocalFileUtils.isExisting(fname) )
								continue;
							MatrixBlock buffer = LocalFileUtils.readMatrixBlockFromLocal(fname);
							for( int i=0; i<buffer.getNumRows(); i++ )
								for( int j=0; j<buffer.getNumColumns(); j++ )
								{
									double lvalue = buffer.quickGetValue(i, j);
									if( lvalue != 0 )
										flags[ i ] = false;
								}
						}
						else{
							LinkedList<Cell> buffer = StagingFileUtils.readCellListFromLocal(fname);
							for( Cell c : buffer )
								flags[ (int)c.getRow()-blockRow*brlen-1 ] = false;
						}
					} 
			
					//create and append key mapping
					LinkedList<long[]> keyMapping = new LinkedList<long[]>();
					for( int i = 0; i<flags.length; i++ )
						if( !flags[i] )
							keyMapping.add(new long[]{blockRow*brlen+i, lastKey++});
					len += keyMapping.size();
					StagingFileUtils.writeKeyMappingToLocal(metaOut, keyMapping.toArray(new long[0][0]));
				}
			}
			else
			{
				for(int blockCol = 0; blockCol < (int)Math.ceil(clen/(double)bclen); blockCol++)
				{	
					boolean[] flags = new boolean[bclen];
					for( int k=0; k<bclen; k++ )
						flags[k] = true;
					
					//scan for empty rows
					for(int blockRow = 0; blockRow < (int)Math.ceil(rlen/(double)brlen); blockRow++)
					{
						String fname = stagingDir+"/"+(blockRow+1)+"_"+(blockCol+1);
						if( ii == InputInfo.BinaryBlockInputInfo ){
							if( !LocalFileUtils.isExisting(fname) )
								continue;
							MatrixBlock buffer = LocalFileUtils.readMatrixBlockFromLocal(fname);
							for( int i=0; i<buffer.getNumRows(); i++ )
								for( int j=0; j<buffer.getNumColumns(); j++ )
								{
									double lvalue = buffer.quickGetValue(i, j);
									if( lvalue != 0 )
										flags[ j ] = false;
								}
						}
						else{
							LinkedList<Cell> buffer = StagingFileUtils.readCellListFromLocal(fname);
							for( Cell c : buffer )
								flags[ (int)c.getCol()-blockCol*bclen-1 ] = false;
						}
					} 
			
					//create and append key mapping
					LinkedList<long[]> keyMapping = new LinkedList<long[]>();
					for( int i = 0; i<flags.length; i++ )
						if( !flags[i] )
							keyMapping.add(new long[]{blockCol*bclen+i, lastKey++});
					len += keyMapping.size();
					StagingFileUtils.writeKeyMappingToLocal(metaOut, keyMapping.toArray(new long[0][0]));
				}
			}
			
			//final validation (matrices with dimensions 0x0 not allowed)
			if( len <= 0 )
				throw new DMLRuntimeException("Matrices with dimensions [0,0] not supported.");
			
			return len;
		}

		private long createKeyMappingDiag( String stagingDir, long rlen, long clen, int brlen, int bclen, InputInfo ii) 
			throws FileNotFoundException, IOException, DMLRuntimeException 
		{
			String metaOut = stagingDir+"/meta";
			
			long len = 0;
			long lastKey = 0;
			
			if(_margin.equals("rows"))
			{
				for(int blockRow = 0; blockRow < (int)Math.ceil(rlen/(double)brlen); blockRow++)
				{	
					boolean[] flags = new boolean[brlen];
					for( int k=0; k<brlen; k++ )
						flags[k] = true;
					
					//scan for empty rows
					String fname = stagingDir+"/"+(blockRow+1)+"_"+(blockRow+1);
					if( ii == InputInfo.BinaryBlockInputInfo ){
						if( !LocalFileUtils.isExisting(fname) )
							continue;
						MatrixBlock buffer = LocalFileUtils.readMatrixBlockFromLocal(fname);
						for( int i=0; i<buffer.getNumRows(); i++ )
							for( int j=0; j<buffer.getNumColumns(); j++ )
							{
								double lvalue = buffer.quickGetValue(i, j);
								if( lvalue != 0 )
									flags[ i ] = false;
							}
					}
					else{
						LinkedList<Cell> buffer = StagingFileUtils.readCellListFromLocal(fname);
						for( Cell c : buffer )
							flags[ (int)c.getRow()-blockRow*brlen-1 ] = false;
					}
					 
			
					//create and append key mapping
					LinkedList<long[]> keyMapping = new LinkedList<long[]>();
					for( int i = 0; i<flags.length; i++ )
						if( !flags[i] )
							keyMapping.add(new long[]{blockRow*brlen+i, lastKey++});
					len += keyMapping.size();
					StagingFileUtils.writeKeyMappingToLocal(metaOut, keyMapping.toArray(new long[0][0]));
				}
			}
			else
			{
				for(int blockCol = 0; blockCol < (int)Math.ceil(clen/(double)bclen); blockCol++)
				{	
					boolean[] flags = new boolean[bclen];
					for( int k=0; k<bclen; k++ )
						flags[k] = true;
					
					//scan for empty rows
					String fname = stagingDir+"/"+(blockCol+1)+"_"+(blockCol+1);
					if( ii == InputInfo.BinaryBlockInputInfo ){
						if( !LocalFileUtils.isExisting(fname) )
							continue;
						MatrixBlock buffer = LocalFileUtils.readMatrixBlockFromLocal(fname);
						for( int i=0; i<buffer.getNumRows(); i++ )
							for( int j=0; j<buffer.getNumColumns(); j++ )
							{
								double lvalue = buffer.quickGetValue(i, j);
								if( lvalue != 0 )
									flags[ j ] = false;
							}
					}
					else{
						LinkedList<Cell> buffer = StagingFileUtils.readCellListFromLocal(fname);
						for( Cell c : buffer )
							flags[ (int)c.getCol()-blockCol*bclen-1 ] = false;
					}
					 
			
					//create and append key mapping
					LinkedList<long[]> keyMapping = new LinkedList<long[]>();
					for( int i = 0; i<flags.length; i++ )
						if( !flags[i] )
							keyMapping.add(new long[]{blockCol*bclen+i, lastKey++});
					len += keyMapping.size();
					StagingFileUtils.writeKeyMappingToLocal(metaOut, keyMapping.toArray(new long[0][0]));
				}
			}
			
			//final validation (matrices with dimensions 0x0 not allowed)
			if( len <= 0 )
				throw new DMLRuntimeException("Matrices with dimensions [0,0] not supported.");
			
			return len;
		}

		@SuppressWarnings("deprecation")
		public void createCellResultFile( String fnameNew, String stagingDir, long rlen, long clen, int brlen, int bclen, InputInfo ii ) 
			throws IOException, DMLRuntimeException
		{
			//prepare input
			JobConf job = new JobConf(ConfigurationManager.getCachedJobConf());	
			Path path = new Path(fnameNew);
			FileSystem fs = IOUtilFunctions.getFileSystem(path, job);
			String metaOut = stagingDir+"/meta";

			//prepare output
			BufferedWriter twriter = null;			
			SequenceFile.Writer bwriter = null; 
			if( ii == InputInfo.TextCellInputInfo )
				twriter = new BufferedWriter(new OutputStreamWriter(fs.create(path,true)));	
			else if( ii == InputInfo.BinaryCellInputInfo )
				bwriter = new SequenceFile.Writer(fs, job, path, MatrixIndexes.class, MatrixCell.class);
			else
				throw new DMLRuntimeException("Unsupported cell input info: "+InputInfo.inputInfoToString(ii));
			
			StringBuilder sb = new StringBuilder();
			MatrixIndexes key = new MatrixIndexes();
			MatrixCell value = new MatrixCell();

			HashMap<Integer,HashMap<Long,Long>> keyMap = new HashMap<Integer, HashMap<Long,Long>>();
			BufferedReader fkeyMap = StagingFileUtils.openKeyMap(metaOut);
			try
			{
				if( _margin.equals("rows") )
				{
					for(int blockRow = 0; blockRow < (int)Math.ceil(rlen/(double)brlen); blockRow++)
					{
						StagingFileUtils.nextKeyMap(fkeyMap, keyMap, blockRow, brlen);		
						for(int blockCol = 0; blockCol < (int)Math.ceil(clen/(double)bclen); blockCol++)
						{
							String fname = stagingDir+"/"+(blockRow+1)+"_"+(blockCol+1);
							LinkedList<Cell> buffer = StagingFileUtils.readCellListFromLocal(fname);
							if( ii == InputInfo.TextCellInputInfo )
								for( Cell c : buffer )
								{
									sb.append(keyMap.get(blockRow).get(c.getRow()-1)+1);
									sb.append(' ');
									sb.append(c.getCol());
									sb.append(' ');
									sb.append(c.getValue());
									sb.append('\n');
									twriter.write( sb.toString() );	
									sb.setLength(0);
								}
							else if( ii == InputInfo.BinaryCellInputInfo )
								for( Cell c : buffer )
								{
									key.setIndexes(keyMap.get(blockRow).get(c.getRow()-1)+1, c.getCol());
									value.setValue(c.getValue());
									bwriter.append(key, value);	
								}
						}
						keyMap.remove(blockRow);
					}
				}
				else
				{
					for(int blockCol = 0; blockCol < (int)Math.ceil(clen/(double)bclen); blockCol++)
					{
						StagingFileUtils.nextKeyMap(fkeyMap, keyMap, blockCol, bclen);		
						for(int blockRow = 0; blockRow < (int)Math.ceil(rlen/(double)brlen); blockRow++)
						{
							String fname = stagingDir+"/"+(blockRow+1)+"_"+(blockCol+1);
							LinkedList<Cell> buffer = StagingFileUtils.readCellListFromLocal(fname);
							if( ii == InputInfo.TextCellInputInfo )
								for( Cell c : buffer )
								{
									sb.append(c.getRow());
									sb.append(' ');
									sb.append(keyMap.get(blockCol).get(c.getCol()-1)+1);
									sb.append(' ');
									sb.append(c.getValue());
									sb.append('\n');
									twriter.write( sb.toString() );	
									sb.setLength(0);
								}
							else if( ii == InputInfo.BinaryCellInputInfo )
								for( Cell c : buffer )
								{
									key.setIndexes(c.getRow(), keyMap.get(blockCol).get(c.getCol()-1)+1);
									value.setValue(c.getValue());
									bwriter.append(key, value);	
								}
						}
						keyMap.remove(blockCol);
					}
				}

				//Note: no need to handle empty result
			}
			finally {
				IOUtilFunctions.closeSilently(fkeyMap);
				IOUtilFunctions.closeSilently(twriter);
				IOUtilFunctions.closeSilently(bwriter);
			}
		}

		@SuppressWarnings("deprecation")
		public void createBlockResultFile( String fnameNew, String stagingDir, long rlen, long clen, long newlen, long nnz, int brlen, int bclen, InputInfo ii ) 
			throws IOException, DMLRuntimeException
		{
			//prepare input
			JobConf job = new JobConf(ConfigurationManager.getCachedJobConf());	
			Path path = new Path(fnameNew);
			FileSystem fs = IOUtilFunctions.getFileSystem(path, job);
			String metaOut = stagingDir+"/meta";
	
			//prepare output
			SequenceFile.Writer writer = new SequenceFile.Writer(fs, job, path, MatrixIndexes.class, MatrixBlock.class);
			
			MatrixIndexes key = new MatrixIndexes(); 
			
			try
			{
				if( _margin.equals("rows") ) 
				{
					MatrixBlock[] blocks = MatrixWriter.createMatrixBlocksForReuse(newlen, clen, brlen, bclen, 
							                     MatrixBlock.evalSparseFormatInMemory(rlen, clen, nnz), nnz);  
					
					for(int blockCol = 0; blockCol < (int)Math.ceil(clen/(double)bclen); blockCol++)
					{
						HashMap<Integer,HashMap<Long,Long>> keyMap = new HashMap<Integer, HashMap<Long,Long>>();
						BufferedReader fkeyMap = StagingFileUtils.openKeyMap(metaOut);
						int maxCol = (int)(((long)blockCol*bclen + bclen < clen) ? bclen : clen - (long)blockCol*bclen);
						
						int blockRowOut = 0;
						int currentSize = -1;
						while( (currentSize = StagingFileUtils.nextSizedKeyMap(fkeyMap, keyMap, brlen, brlen)) > 0  )
						{
							int maxRow = currentSize;
							
							//get reuse matrix block
							MatrixBlock block = MatrixWriter.getMatrixBlockForReuse(blocks, maxRow, maxCol, brlen, bclen);
							block.reset(maxRow, maxCol);
							
							int rowPos = 0;
							int blockRow = Collections.min(keyMap.keySet());
							
							for( ; blockRow < (int)Math.ceil(rlen/(double)brlen) && rowPos<brlen ; blockRow++)
							{
								if( keyMap.containsKey(blockRow) )
								{
									String fname = stagingDir+"/"+(blockRow+1)+"_"+(blockCol+1);
									
									if( LocalFileUtils.isExisting(fname) ) 
									{	
										MatrixBlock tmp = LocalFileUtils.readMatrixBlockFromLocal(fname);
										
										HashMap<Long,Long> lkeyMap = keyMap.get(blockRow);
										long row_offset = (long)blockRow*brlen;
										for( int i=0; i<tmp.getNumRows(); i++ )
											if( lkeyMap.containsKey(row_offset+i) ) {	
												//copy row
												for( int j=0; j<tmp.getNumColumns(); j++ ) {
													double lvalue = tmp.quickGetValue(i, j);
													if( lvalue != 0 )
														block.quickSetValue(rowPos, j, lvalue);
												}
												rowPos++;
											}
									}
									else
									{
										HashMap<Long,Long> lkeyMap = keyMap.get(blockRow);
										rowPos+=lkeyMap.size();
									}
								}				
								keyMap.remove(blockRow);
							}
							
							key.setIndexes(blockRowOut+1, blockCol+1);
							writer.append(key, block);
							blockRowOut++;
						}
						
						IOUtilFunctions.closeSilently(fkeyMap);
					}
				}
				else
				{
					MatrixBlock[] blocks = MatrixWriter.createMatrixBlocksForReuse(rlen, newlen, brlen, bclen, 
							                    MatrixBlock.evalSparseFormatInMemory(rlen, clen, nnz), nnz);  
					
					for(int blockRow = 0; blockRow < (int)Math.ceil(rlen/(double)brlen); blockRow++)
					{
						HashMap<Integer,HashMap<Long,Long>> keyMap = new HashMap<Integer, HashMap<Long,Long>>();
						BufferedReader fkeyMap = StagingFileUtils.openKeyMap(metaOut);
						int maxRow = (int)(((long)blockRow*brlen + brlen < rlen) ? brlen : rlen - (long)blockRow*brlen);
						
						int blockColOut = 0;
						int currentSize = -1;
						while( (currentSize = StagingFileUtils.nextSizedKeyMap(fkeyMap, keyMap, bclen, bclen)) > 0  )
						{
							int maxCol = currentSize;
							
							//get reuse matrix block
							MatrixBlock block = MatrixWriter.getMatrixBlockForReuse(blocks, maxRow, maxCol, brlen, bclen);
							block.reset(maxRow, maxCol);
							int colPos = 0;
							
							int blockCol = Collections.min(keyMap.keySet());
							for( ; blockCol < (int)Math.ceil(clen/(double)bclen) && colPos<bclen ; blockCol++)
							{
								if( keyMap.containsKey(blockCol) )
								{
									String fname = stagingDir+"/"+(blockRow+1)+"_"+(blockCol+1);
									
									if( LocalFileUtils.isExisting(fname) ) 
									{
										MatrixBlock tmp = LocalFileUtils.readMatrixBlockFromLocal(fname);
										
										HashMap<Long,Long> lkeyMap = keyMap.get(blockCol);
										long col_offset = blockCol*bclen;
										for( int j=0; j<tmp.getNumColumns(); j++ )
											if( lkeyMap.containsKey(col_offset+j) ) {	
												//copy column
												for( int i=0; i<tmp.getNumRows(); i++ ){
													double lvalue = tmp.quickGetValue(i, j);
													if( lvalue != 0 )
														block.quickSetValue(i, colPos, lvalue);
												}
												colPos++;
											}
									}
									else
									{
										HashMap<Long,Long> lkeyMap = keyMap.get(blockCol);
										colPos+=lkeyMap.size();
									}
								}							
								keyMap.remove(blockCol);
							}
							
							key.setIndexes(blockRow+1, blockColOut+1);
							writer.append(key, block);
							blockColOut++;
						}
						IOUtilFunctions.closeSilently(fkeyMap);
					}
				}
				
				//Note: no handling of empty matrices necessary
			}
			finally {
				IOUtilFunctions.closeSilently(writer);
			}
		}

		@SuppressWarnings("deprecation")
		public void createBlockResultFileDiag( String fnameNew, String stagingDir, long rlen, long clen, long newlen, long nnz, int brlen, int bclen, InputInfo ii ) 
			throws IOException, DMLRuntimeException
		{
			//prepare input
			JobConf job = new JobConf(ConfigurationManager.getCachedJobConf());	
			Path path = new Path(fnameNew);
			FileSystem fs = IOUtilFunctions.getFileSystem(path, job);
			String metaOut = stagingDir+"/meta";
	
			//prepare output
			SequenceFile.Writer writer = new SequenceFile.Writer(fs, job, path, MatrixIndexes.class, MatrixBlock.class);
			MatrixIndexes key = new MatrixIndexes(); 
			HashSet<Long> writtenBlocks = new HashSet<Long>();
			
			try
			{
				if( _margin.equals("rows") ) 
				{
					MatrixBlock[] blocks = MatrixWriter.createMatrixBlocksForReuse(newlen, clen, brlen, bclen, 
							                       MatrixBlock.evalSparseFormatInMemory(rlen, clen, nnz), nnz);  
					HashMap<Integer,HashMap<Long,Long>> keyMap = new HashMap<Integer, HashMap<Long,Long>>();
					BufferedReader fkeyMap = StagingFileUtils.openKeyMap(metaOut);
					int currentSize = -1;
					int blockRowOut = 0;
					
					while( (currentSize = StagingFileUtils.nextSizedKeyMap(fkeyMap, keyMap, brlen, brlen)) > 0  )
					{
						int rowPos = 0;
						int blockRow = Collections.min(keyMap.keySet()); 
						int maxRow = currentSize;
						for( ; blockRow < (int)Math.ceil(rlen/(double)brlen); blockRow++)
						{
							int blockCol = blockRow; // for diag known to be equivalent
							int maxCol = (int)(((long)blockCol*bclen + bclen < clen) ? bclen : clen - (long)blockCol*bclen);
							
							//get reuse matrix block
							MatrixBlock block = MatrixWriter.getMatrixBlockForReuse(blocks, maxRow, maxCol, brlen, bclen);
							block.reset(maxRow, maxCol);
							
							if( keyMap.containsKey(blockRow) )
							{
								String fname = stagingDir+"/"+(blockRow+1)+"_"+(blockCol+1);
								MatrixBlock tmp = LocalFileUtils.readMatrixBlockFromLocal(fname);
								
								HashMap<Long,Long> lkeyMap = keyMap.get(blockRow);
								long row_offset = blockRow*brlen;
								for( int i=0; i<tmp.getNumRows(); i++ )
									if( lkeyMap.containsKey(row_offset+i) ) {	
										//copy row
										for( int j=0; j<tmp.getNumColumns(); j++ ) {
											double lvalue = tmp.quickGetValue(i, j);
											if( lvalue != 0 )
												block.quickSetValue(rowPos, j, lvalue);
										}
										rowPos++;
									}
							}
							
							//output current block (by def of diagBlocks, no additional rows)
							key.setIndexes(blockRowOut+1, blockCol+1);
							writer.append(key, block);
							writtenBlocks.add(IDHandler.concatIntIDsToLong(blockRowOut+1, blockCol+1));
							
							//finished block
							if( rowPos == maxRow )
							{
								keyMap.remove(blockRow); 	
								blockRowOut++;
								break;
							}
						}
					}
					IOUtilFunctions.closeSilently(fkeyMap);
				}
				else //cols
				{
					MatrixBlock[] blocks = MatrixWriter.createMatrixBlocksForReuse(rlen, newlen, brlen, bclen, 
							                     MatrixBlock.evalSparseFormatInMemory(rlen, clen, nnz), nnz);  
					HashMap<Integer,HashMap<Long,Long>> keyMap = new HashMap<Integer, HashMap<Long,Long>>();
					BufferedReader fkeyMap = StagingFileUtils.openKeyMap(metaOut);
					int currentSize = -1;
					int blockColOut = 0;
					
					while( (currentSize = StagingFileUtils.nextSizedKeyMap(fkeyMap, keyMap, bclen, bclen)) > 0  )
					{
						int colPos = 0;
						int blockCol = Collections.min(keyMap.keySet()); 
						int maxCol = currentSize;
						for( ; blockCol < (int)Math.ceil(clen/(double)bclen); blockCol++)
						{
							int blockRow = blockCol; // for diag known to be equivalent
							int maxRow = (int)((blockRow*brlen + brlen < rlen) ? brlen : rlen - blockRow*brlen);
							
							//get reuse matrix block
							MatrixBlock block = MatrixWriter.getMatrixBlockForReuse(blocks, maxRow, maxCol, brlen, bclen);
							block.reset(maxRow, maxCol);
						
							if( keyMap.containsKey(blockCol) )
							{
								String fname = stagingDir+"/"+(blockRow+1)+"_"+(blockCol+1);
								MatrixBlock tmp = LocalFileUtils.readMatrixBlockFromLocal(fname);
								
								HashMap<Long,Long> lkeyMap = keyMap.get(blockCol);
								long col_offset = blockCol*bclen;
								for( int j=0; j<tmp.getNumColumns(); j++ )
									if( lkeyMap.containsKey(col_offset+j) ) {	
										//copy column
										for( int i=0; i<tmp.getNumRows(); i++ ){
											double lvalue = tmp.quickGetValue(i, j);
											if( lvalue != 0 )
												block.quickSetValue(i, colPos, lvalue);
										}
										colPos++;
									}
							}
								
							//output current block (by def of diagBlocks, no additional cols)
							key.setIndexes(blockRow+1, blockColOut+1);
							writer.append(key, block);
							writtenBlocks.add(IDHandler.concatIntIDsToLong(blockRow+1, blockColOut+1));
							
							//finished block
							if( colPos == maxCol )
							{
								keyMap.remove(blockCol); 	
								blockColOut++;
								break;
							}
						}
					}
					IOUtilFunctions.closeSilently(fkeyMap);
				}
				
				//write remaining empty blocks
				MatrixBlock empty = new MatrixBlock(1,1,true);
				long rows = _margin.equals("rows") ? newlen : rlen;
				long cols = _margin.equals("cols") ? newlen : clen;
				int countBlk1 = (int)Math.ceil(rows/(double)brlen)*(int)Math.ceil(cols/(double)bclen);
				int countBlk2 = writtenBlocks.size();
				for( int i=0; i<(int)Math.ceil(rows/(double)brlen); i++)
					for(int j=0; j<(int)Math.ceil(cols/(double)bclen); j++ )
						if( !writtenBlocks.contains(IDHandler.concatIntIDsToLong(i+1, j+1)) )
						{
							int maxRow = (int)((i*brlen + brlen < rows) ? brlen : rows - i*brlen);
							int maxCol = (int)((j*bclen + bclen < cols) ? bclen : cols - j*bclen);
							empty.reset(maxRow, maxCol);
							key.setIndexes(i+1, j+1);
							writer.append(key, empty);
							countBlk2++;
						}
				
				if( countBlk1 != countBlk2 )
					throw new DMLRuntimeException("Wrong number of written result blocks: "+countBlk1+" vs "+countBlk2+".");
			}
			finally {
				IOUtilFunctions.closeSilently(writer);
			}
		}
	}
}

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
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;

import org.apache.hadoop.fs.BlockLocation;
import org.apache.hadoop.fs.FileStatus;
import org.apache.hadoop.fs.FileSystem;
import org.apache.hadoop.fs.Path;
import org.apache.hadoop.io.LongWritable;
import org.apache.hadoop.io.Text;
import org.apache.hadoop.mapred.FileSplit;
import org.apache.hadoop.mapred.JobConf;
import org.apache.hadoop.mapred.RecordReader;
import org.apache.hadoop.mapred.Reporter;
import org.apache.hadoop.mapred.lib.NLineInputFormat;

import org.apache.sysml.conf.ConfigurationManager;
import org.apache.sysml.runtime.controlprogram.parfor.Task.TaskType;
import org.apache.sysml.runtime.instructions.cp.IntObject;
import org.apache.sysml.runtime.io.IOUtilFunctions;


/**
 * Wrapper for arbitrary input split in order to attach our co-location information.
 * 
 */
public class RemoteParForColocatedFileSplit extends FileSplit
{
	private String _fname = null;
	private int    _blen  = 1;
	
	/**
	 * Required because hadoop explicitly accesses this private constructor
	 * via reflection (since private not inherited from FileSplit).
	 */
	@SuppressWarnings("unused")
	private RemoteParForColocatedFileSplit() {
		super( null, -1, -1, new String[]{} );
	}
	
	public RemoteParForColocatedFileSplit( FileSplit split, String fname, int blen ) 
		throws IOException 
	{
		super( split.getPath(), split.getStart(), split.getLength(), split.getLocations() );
		
		_fname = fname;
		_blen = blen;
	}

	/**
	 * Get the list of hostnames where the input split is located.
	 */
	@Override
	public String[] getLocations() throws IOException
	{
		//Timing time = new Timing();
		//time.start();
		
		JobConf job = new JobConf(ConfigurationManager.getCachedJobConf());
		FileSystem fs = IOUtilFunctions.getFileSystem(getPath(), job);
		
		//read task string
		LongWritable key = new LongWritable();
		Text value = new Text();
		RecordReader<LongWritable,Text> reader = null;
		try {
			reader = new NLineInputFormat().getRecordReader(this, job, Reporter.NULL);
			reader.next(key, value);
		}
		finally {
			IOUtilFunctions.closeSilently(reader);
		}
		
		//parse task
		Task t = Task.parseCompactString( value.toString() );
		
		//get all locations
		HashMap<String, Integer> hosts = new HashMap<>();
		
		if( t.getType() == TaskType.SET )
		{
			for( IntObject val : t.getIterations() )
			{
				String fname = _fname+"/"+String.valueOf(((val.getLongValue()-1)/_blen+1));
				FileStatus status = fs.getFileStatus(new Path(fname)); 
				BlockLocation[] tmp1 = fs.getFileBlockLocations(status, 0, status.getLen());
				for( BlockLocation bl : tmp1 )
					countHosts(hosts, bl.getHosts());
			}
		}
		else //TaskType.RANGE
		{
			//since this is a serial process, we use just the first iteration
			//as a heuristic for location information
			long lFrom  = t.getIterations().get(0).getLongValue();
			long lTo  = t.getIterations().get(1).getLongValue();
			for( long li : new long[]{lFrom,lTo} )
			{
				String fname = _fname+"/"+String.valueOf( ((li-1)/_blen+1) );
				FileStatus status = fs.getFileStatus(new Path(fname)); 
				BlockLocation[] tmp1 = fs.getFileBlockLocations(status, 0, status.getLen());
				for( BlockLocation bl : tmp1 )
					countHosts(hosts, bl.getHosts());
			}
		}
		
		//majority consensus on top host
		return getTopHosts(hosts);
	}

	private static void countHosts( HashMap<String,Integer> hosts, String[] names ) {
		for( String name : names ) {
			Integer tmp = hosts.get(name);
			if( tmp != null )
				hosts.put(name, tmp+1);
			else
				hosts.put(name, 1);
		}
	}

	private static String[] getTopHosts( HashMap<String,Integer> hosts ) {
		int max = Integer.MIN_VALUE;
		HashSet<String> maxName = new HashSet<>();
		for( Entry<String,Integer> e : hosts.entrySet() )
			if( e.getValue() > max ) {
				maxName.clear();
				max = e.getValue();
				maxName.add(e.getKey());
			}
			else if( e.getValue() == max )
				maxName.add(e.getKey());
		return maxName.toArray(new String[0]);
	}
}

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

package org.apache.sysml.yarn;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import org.apache.commons.logging.Log;
import org.apache.commons.logging.LogFactory;
import org.apache.hadoop.fs.FSDataOutputStream;
import org.apache.hadoop.fs.FileStatus;
import org.apache.hadoop.fs.FileSystem;
import org.apache.hadoop.fs.FileUtil;
import org.apache.hadoop.fs.Path;
import org.apache.hadoop.mapreduce.v2.util.MRApps;
import org.apache.hadoop.yarn.api.ApplicationConstants;
import org.apache.hadoop.yarn.api.ApplicationConstants.Environment;
import org.apache.hadoop.yarn.api.records.ApplicationId;
import org.apache.hadoop.yarn.api.records.ApplicationReport;
import org.apache.hadoop.yarn.api.records.ApplicationSubmissionContext;
import org.apache.hadoop.yarn.api.records.ContainerLaunchContext;
import org.apache.hadoop.yarn.api.records.FinalApplicationStatus;
import org.apache.hadoop.yarn.api.records.LocalResource;
import org.apache.hadoop.yarn.api.records.LocalResourceType;
import org.apache.hadoop.yarn.api.records.LocalResourceVisibility;
import org.apache.hadoop.yarn.api.records.Resource;
import org.apache.hadoop.yarn.api.records.YarnApplicationState;
import org.apache.hadoop.yarn.client.api.YarnClient;
import org.apache.hadoop.yarn.client.api.YarnClientApplication;
import org.apache.hadoop.yarn.conf.YarnConfiguration;
import org.apache.hadoop.yarn.util.ConverterUtils;
import org.apache.hadoop.yarn.util.Records;
import org.apache.sysml.conf.DMLConfig;
import org.apache.sysml.runtime.DMLRuntimeException;
import org.apache.sysml.runtime.DMLScriptException;
import org.apache.sysml.runtime.controlprogram.parfor.stat.Timing;
import org.apache.sysml.runtime.io.IOUtilFunctions;
import org.apache.sysml.runtime.util.MapReduceTool;

/**
 * NOTES:
 *   * Security: By default, submitted applications are ran as user 'yarn'. 
 *     In order to allow for security and relative filenames on hdfs (/user/&lt;username&gt;/.), 
 *     we can configure the LinuxContainerExecutor in yarn-site.xml, which runs the
 *     application as the user who submits the application.
 *   * SystemML.jar file dependency: We need to submit the SystemML.jar along with the
 *     application. Unfortunately, hadoop jar unpacks the jar such that we dont get a handle
 *     to the original jar filename. We currently parse the constant IBM_JAVA_COMMAND_LINE
 *     to get the jar filename. For robustness, we fall back to repackaging the unzipped files
 *     to a jar if this constant does not exist.  
 * 
 */
public class DMLYarnClient 
{
		
	private static final Log LOG = LogFactory.getLog(DMLYarnClient.class);
	
	//Internal configuration parameters
	// environment variable to obtain the original jar filename
	public static final String JARFILE_ENV_CONST = "IBM_JAVA_COMMAND_LINE"; 
	// environment variable to obtain default jvm arguments
	public static final String JVMOPTS_ENV_CONST = "HADOOP_OPTS";
	// environment variable to obtain mapred home (for robustness only)
	public static final String MAPRED_HOME_ENV_CONST = "HADOOP_MAPRED_HOME";
	public static final String HADOOP_HOME_ENV_CONST = "HADOOP_HOME";
	// default of 1 core since YARN scheduler does not take the number of cores into account yet 
	public static final int NUM_CORES = 1;  
	// factor for compute virtual memory to request based on given max heap size
	// (if the absolute overhead is larger than a threshold, we use this threshold as a constant overhead)
	public static final double MEM_FACTOR = 1.5; 
	public static final int MAX_MEM_OVERHEAD = 2*1024; //2GB
	// default application state report (in milliseconds)
	public static final int APP_STATE_INTERVAL = 200;
	// default application master name
	public static final String APPMASTER_NAME = "SystemML-AM";
	// default dml script file name for hdfs script serialization
	public static final String DML_SCRIPT_NAME = "script.dml";
	// default dml config file name for hdfs config serialization
	public static final String DML_CONFIG_NAME = "config.xml";
	// default SystemML jar file name for hdfs jar copy
	public static final String DML_JAR_NAME = "SystemML.jar";
	// default dml stop message file name for hdfs message serialization
	public static final String DML_STOPMSG_NAME = "stop_msg.txt";
	
	
	private String _dmlScript = null;
	private DMLConfig _dmlConfig = null;
	private String[] _args = null; 
	
	//hdfs file names local resources
	private String _hdfsJarFile   = null;
	private String _hdfsDMLScript = null;
	private String _hdfsDMLConfig = null;	
	
	/**
	 * Protected since only supposed to be accessed via proxy in same package.
	 * This is to ensure robustness in case of missing yarn libraries.
	 * 
	 * @param dmlScriptStr script string
	 * @param conf dml configuration
	 * @param args arguments
	 */
	protected DMLYarnClient(String dmlScriptStr, DMLConfig conf, String[] args)
	{
		_dmlScript = dmlScriptStr;
		_dmlConfig = conf;
		_args = args;
	}
	
	
	/**
	 * Method to launch the dml yarn app master and execute the given dml script
	 * with the given configuration and jar file.
	 * 
	 * NOTE: on launching the yarn app master, we do not explicitly probe if we
	 *	  are running on a yarn or MR1 cluster. In case of MR1, already the class 
	 *	  YarnConfiguration will not be found and raise a classnotfound. In case of any 
	 *	  exception we fall back to run CP directly in the client process.
	 * 
	 * @return true if dml program successfully executed as yarn app master
	 * @throws IOException if IOException occurs
	 * @throws DMLScriptException if DMLScriptException occurs
	 */
	protected boolean launchDMLYarnAppmaster() 
		throws IOException, DMLScriptException
	{
		boolean ret = false;
		String hdfsWD = null;
		
		try
		{
			Timing time = new Timing(true);
			
			// load yarn configuration
			YarnConfiguration yconf = new YarnConfiguration();
			
			// create yarn client
			YarnClient yarnClient = YarnClient.createYarnClient();
			yarnClient.init(yconf);
			yarnClient.start();
			
			// create application and get the ApplicationID
			YarnClientApplication app = yarnClient.createApplication();
			ApplicationSubmissionContext appContext = app.getApplicationSubmissionContext();
			ApplicationId appId = appContext.getApplicationId();
			LOG.debug("Created application (applicationID: "+appId+")");
			
			// prepare hdfs working directory via ApplicationID
			// copy script, config, jar file to hdfs
			hdfsWD = DMLAppMasterUtils.constructHDFSWorkingDir(_dmlConfig, appId);
			copyResourcesToHdfsWorkingDir(yconf, hdfsWD);
			
			//construct command line argument
			String command = constructAMCommand(_args, _dmlConfig);
			LOG.debug("Constructed application master command: \n"+command);
			
			// set up the container launch context for the application master
			ContainerLaunchContext amContainer = Records.newRecord(ContainerLaunchContext.class);
			amContainer.setCommands( Collections.singletonList(command) );
			amContainer.setLocalResources( constructLocalResourceMap(yconf) );
			amContainer.setEnvironment( constructEnvionmentMap(yconf) );

			// Set up resource type requirements for ApplicationMaster
			int memHeap = _dmlConfig.getIntValue(DMLConfig.YARN_APPMASTERMEM);
			int memAlloc = (int) computeMemoryAllocation(memHeap);
			Resource capability = Records.newRecord(Resource.class);
			capability.setMemory( memAlloc );
			capability.setVirtualCores( NUM_CORES );
			LOG.debug("Requested application resources: memory="+memAlloc+", vcores="+NUM_CORES);

			// Finally, set-up ApplicationSubmissionContext for the application
			String qname = _dmlConfig.getTextValue(DMLConfig.YARN_APPQUEUE);
			appContext.setApplicationName(APPMASTER_NAME); // application name
			appContext.setAMContainerSpec(amContainer);
			appContext.setResource(capability);
			appContext.setQueue(qname); // queue
			LOG.debug("Configured application meta data: name="+APPMASTER_NAME+", queue="+qname);
			
			// submit application (non-blocking)
			yarnClient.submitApplication(appContext);

			// Check application status periodically (and output web ui address)
			ApplicationReport appReport = yarnClient.getApplicationReport(appId);
			LOG.info("Application tracking-URL: "+appReport.getTrackingUrl());
			YarnApplicationState appState = appReport.getYarnApplicationState();
			YarnApplicationState oldState = appState;
			LOG.info("Application state: " + appState);
			while( appState != YarnApplicationState.FINISHED
					&& appState != YarnApplicationState.KILLED
					&& appState != YarnApplicationState.FAILED ) 
			{
				Thread.sleep(APP_STATE_INTERVAL); //wait for 200ms
				appReport = yarnClient.getApplicationReport(appId);
				appState = appReport.getYarnApplicationState();
				if( appState != oldState ) {
					oldState = appState;
					LOG.info("Application state: " + appState);
				}
			}
			//check final status (failed or succeeded)
			FinalApplicationStatus finalState = appReport.getFinalApplicationStatus();
			LOG.info("Application final status: " + finalState);
			
			//show application and total runtime
			double appRuntime = (double)(appReport.getFinishTime() - appReport.getStartTime()) / 1000;
			LOG.info( "Application runtime: " + appRuntime + " sec." );
			LOG.info( "Total runtime: " + String.format("%.3f", time.stop()/1000) + " sec.");
			
			//raised script-level error in case of failed final status
			if( finalState != FinalApplicationStatus.SUCCEEDED )
			{
				//propagate script-level stop call message
				String stop_msg = readMessageToHDFSWorkingDir(_dmlConfig, yconf, appId);
				if( stop_msg != null ) 
					throw new DMLScriptException(stop_msg);
				
				//generic failure message
				throw new DMLRuntimeException("DML yarn app master finished with final status: "+finalState+".");
			}
			
			ret = true;
		}
		catch(DMLScriptException ex) {
			//rethrow DMLScriptException to propagate stop call
			throw ex;
		}
		catch(Exception ex) {
			LOG.error("Failed to run DML yarn app master.", ex);
			ret = false;
		}
		finally
		{
			//cleanup working directory
			if( hdfsWD != null )
				MapReduceTool.deleteFileIfExistOnHDFS(hdfsWD);
		}
		
		return ret;
	}

	@SuppressWarnings("deprecation")
	private void copyResourcesToHdfsWorkingDir( YarnConfiguration yconf, String hdfsWD ) 
		throws IOException, InterruptedException 
	{
		Path confPath = new Path(hdfsWD, DML_CONFIG_NAME);
		FileSystem fs = IOUtilFunctions.getFileSystem(confPath, yconf);
		
		//create working directory
		MapReduceTool.createDirIfNotExistOnHDFS(confPath, DMLConfig.DEFAULT_SHARED_DIR_PERMISSION);
		
		//serialize the dml config to HDFS file 
		//NOTE: we do not modify and ship the absolute scratch space path of the current user
		//because this might result in permission issues if the app master is run with a different user
		//(runtime plan migration during resource reoptimizations now needs to use qualified names
		//for shipping/reading intermediates) TODO modify resource reoptimizer on prototype integration.
		try( FSDataOutputStream fout = fs.create(confPath, true) ) {
			fout.writeBytes(_dmlConfig.serializeDMLConfig() + "\n");
		}
		_hdfsDMLConfig = confPath.makeQualified(fs).toString();
		LOG.debug("DML config written to HDFS file: "+_hdfsDMLConfig+"");

		//serialize the dml script to HDFS file
		Path scriptPath = new Path(hdfsWD, DML_SCRIPT_NAME);
		try( FSDataOutputStream fout2 = fs.create(scriptPath, true) ) {
			fout2.writeBytes(_dmlScript);
		}
		_hdfsDMLScript = scriptPath.makeQualified(fs).toString();
		LOG.debug("DML script written to HDFS file: "+_hdfsDMLScript+"");
		
		// copy local jar file to HDFS (try to get the original jar filename)
		String fname = getLocalJarFileNameFromEnvConst();
		if( fname == null ){
			//get location of unpacked jar classes and repackage (if required)
			String lclassFile = DMLYarnClient.class.getProtectionDomain().getCodeSource().getLocation().getPath().toString();
			File flclassFile = new File( lclassFile );
			if( !flclassFile.isDirectory() ) //called w/ jar 
				fname = lclassFile;
			else //called w/ unpacked jar (need to be repackaged)	
				fname = createJar(lclassFile);
		}
		Path srcPath = new Path(fname);
		Path dstPath = new Path(hdfsWD, srcPath.getName());
		FileUtil.copy(FileSystem.getLocal(yconf), srcPath, fs, dstPath, false, true, yconf);
		_hdfsJarFile = dstPath.makeQualified(fs).toString();	
		LOG.debug("Jar file copied from local file: "+srcPath.toString()+" to HDFS file: "+dstPath.toString());
	}
	
	/**
	 * Obtain the local jar file name from the system environment
	 * 
	 * @return null if the constant does not exists
	 */
	private static String getLocalJarFileNameFromEnvConst()
	{
		String fname = null;
		
		try
		{
			//parse environment constants
			Map<String, String> env = System.getenv();
			if( env.containsKey(JARFILE_ENV_CONST) ){
				String tmp = env.get(JARFILE_ENV_CONST);
				String[] tmpargs = tmp.split(" ");
				for( int i=0; i<tmpargs.length && fname==null; i++ )
					if( tmpargs[i]!=null && tmpargs[i].endsWith("RunJar") )
						fname = tmpargs[i+1];
			}
		}
		catch(Exception ex)
		{
			LOG.warn("Failed to parse environment variables ("+ex.getMessage()+")");
			fname = null; //indicate to use fallback strategy
		}
		
		//give warning that we fallback to alternative jar shipping method
		if( LOG.isDebugEnabled() && fname == null ) {
			LOG.warn("Failed to find jar file via environment variable '"+JARFILE_ENV_CONST+"', fallback to jar packaging.");
		}
		
		return fname;
	}
	
	/**
	 * This is our fallback strategy for obtaining our SystemML.jar that we need
	 * to submit as resource for the yarn application. We repackage the unzipped
	 * jar to a temporary jar and later copy it to hdfs.
	 * 
	 * @param dir
	 * @return jar name
	 * @throws IOException if IOException occurs
	 * @throws InterruptedException if InterruptedException occurs
	 */
	private static String createJar( String dir ) 
		throws IOException, InterruptedException
	{
		//construct jar command
		String jarname = dir+"/"+DML_JAR_NAME;
		File fdir = new File(dir);
		File[] tmp = fdir.listFiles();
		StringBuilder flist = new StringBuilder();
		for( File ftmp : tmp ) {
			flist.append(ftmp.getName());
			flist.append(" ");
		}
		
		//get jdk home (property 'java.home' gives jre-home of parent jdk or standalone)
		String javahome = System.getProperty("java.home");
		File fjdkhome = new File(new File(javahome).getParent() + File.separator  + "bin");
		String jarPrefix = "";
		if( fjdkhome.exists() ) { //exists if jdk
			jarPrefix = fjdkhome.getAbsolutePath();
			jarPrefix += File.separator;
		}
		if( jarPrefix.isEmpty() )
			LOG.warn("Failed to find jdk home of running jre (java.home="+javahome+").");
		
		//execute jar command
		String command = jarPrefix+"jar cf "+jarname+" "+flist.subSequence(0, flist.length()-1);
		LOG.debug("Packaging jar of unzipped files: "+command);
		Process child = Runtime.getRuntime().exec(command, null, fdir);		
		int c = 0;
		while ((c = child.getInputStream().read()) != -1)
			System.out.print((char) c);
		while ((c = child.getErrorStream().read()) != -1)
			System.err.print((char) c);
		child.waitFor();
		
		return jarname;
	}

	private String constructAMCommand( String[] args, DMLConfig conf )
	{
		//start command
		StringBuilder command = new StringBuilder();
		command.append(Environment.JAVA_HOME.$$() + "/bin/java");
		
		//add client jvm arguments (concatenation of HADOOP_CLIENT_OPTS and HADOOP_OPTS)
		if( System.getenv().containsKey(JVMOPTS_ENV_CONST) ) {
			String externalArgs = System.getenv(JVMOPTS_ENV_CONST);
			//safe parsing and replacement of redundant Xmx, Xms, Xmn
			if( externalArgs != null ) {
				String[] parts = externalArgs.split(" ");
				for( int i=0; i<parts.length; i++ )
					if( !(   parts[i].startsWith("-Xmx") 
						  || parts[i].startsWith("-Xms") 
						  || parts[i].startsWith("-Xmn") ) ) 
					{
						command.append(" ");
						command.append(parts[i]);
					}
			}
		}	
		
		//add jvm heap configuration (specify xmn for default gcpolicy:gencon)
		int memHeap = conf.getIntValue(DMLConfig.YARN_APPMASTERMEM);
		command.append(" -Xmx"+memHeap+"m");
		command.append(" -Xms"+memHeap+"m");
		command.append(" -Xmn"+(int)(memHeap/10)+"m");
		command.append(' ');
		command.append(DMLAppMaster.class.getName());
	
		//add command line args (modify script and config file path)
		for( int i=0; i<_args.length; i++ )
		{
			String arg = _args[i];
			command.append(' ');
			if( i>0 && _args[i-1].equals("-f") ){
				command.append(_hdfsDMLScript);
				command.append(" -config " + _hdfsDMLConfig);
			}
			else if( _args[i].startsWith("-config") ){
				//ignore because config added with -f
			}
			else	
				command.append(arg);
		}
	
		//setup stdout and stderr logs 
		command.append(" 1>" + ApplicationConstants.LOG_DIR_EXPANSION_VAR + "/stdout");
		command.append(" 2>" + ApplicationConstants.LOG_DIR_EXPANSION_VAR + "/stderr");
	
		return command.toString();
	}

	private Map<String, LocalResource> constructLocalResourceMap(YarnConfiguration yconf) 
		throws IOException 
	{
		Map<String, LocalResource> rMap = new HashMap<>();
		Path path = new Path(_hdfsJarFile); 
		
		LocalResource resource = Records.newRecord(LocalResource.class);
		FileStatus jarStat = IOUtilFunctions
			.getFileSystem(path, yconf).getFileStatus(path);
		resource.setResource(ConverterUtils.getYarnUrlFromPath(path));
		resource.setSize(jarStat.getLen());
		resource.setTimestamp(jarStat.getModificationTime());
		resource.setType(LocalResourceType.FILE);
		resource.setVisibility(LocalResourceVisibility.PUBLIC);
		
		rMap.put(DML_JAR_NAME, resource);
		return rMap;
	}

	private static Map<String, String> constructEnvionmentMap(YarnConfiguration yconf) 
		throws IOException
	{
		Map<String, String> eMap = new HashMap<>();
		
		//setup default app master environment
		StringBuilder classpath = new StringBuilder();
		for (String value : yconf.getStrings(
				YarnConfiguration.YARN_APPLICATION_CLASSPATH,
				YarnConfiguration.DEFAULT_YARN_APPLICATION_CLASSPATH)) 
		{
			if( classpath.length() > 0 )
				classpath.append(File.pathSeparator); 
			classpath.append( value.trim() );
		}
		
		//setup mapreduce appmaster environment (for robustness if not included in default environment)
		//for example, by default HDP 2.2 did not include mapred client libraries in this configuration
		//note: we cannot use MRConfigurationNames.MR_APPLICATION_CLASSPATH because it refers to HDFS and $PWD that needs to be setup
		Map<String, String> env = System.getenv();
		String mapred_home = null;
		//get mapred home via alternative environment variables
		if( env.containsKey(MAPRED_HOME_ENV_CONST) ) {
			mapred_home = env.get(MAPRED_HOME_ENV_CONST);
		} 
		else if ( env.containsKey(HADOOP_HOME_ENV_CONST) ){
			String tmp = env.get(HADOOP_HOME_ENV_CONST);
			mapred_home = tmp + File.separator + ".." + File.separator + "hadoop-mapreduce";
		}
		//concatenate mapred home libs to classpath
		if( mapred_home != null ) {
			if( classpath.length() > 0 )
				classpath.append( File.pathSeparator ); 
			classpath.append( mapred_home + File.separator + "*" );
			classpath.append( File.pathSeparator ); 
			classpath.append( mapred_home + File.separator + "lib" + File.separator + "*" );
		}
		
		eMap.put(Environment.CLASSPATH.name(), classpath.toString());
		MRApps.setClasspath(eMap, yconf);
		
		LOG.debug("Constructed environment classpath: "+classpath.toString());
		
		return eMap;
	}	

	private static String readMessageToHDFSWorkingDir(DMLConfig conf, YarnConfiguration yconf, ApplicationId appId)
	{
		String ret = null;
		
		//construct working directory (consistent with client)
		String hdfsWD = DMLAppMasterUtils.constructHDFSWorkingDir(conf, appId);
		Path msgPath = new Path(hdfsWD, DMLYarnClient.DML_STOPMSG_NAME);
		
		//write given message to hdfs
		try {
			FileSystem fs = IOUtilFunctions.getFileSystem(msgPath, yconf);
			if( fs.exists(msgPath) ) {
				try( BufferedReader br = new BufferedReader(new InputStreamReader(fs.open(msgPath))) ) {
					ret = br.readLine();
				}
				LOG.debug("Stop message read from HDFS file "+msgPath+": "+ret );
			}
		}
		catch(Exception ex) {
			LOG.error("Failed to read stop message from HDFS file: "+msgPath, ex);
		}
		
		return ret;
	}

	public static long computeMemoryAllocation( long heapsize )
	{
		long ret = heapsize;
		
		if( heapsize * MEM_FACTOR - heapsize < MAX_MEM_OVERHEAD )
			ret = (long) (heapsize * MEM_FACTOR);
		else
			ret = heapsize + MAX_MEM_OVERHEAD;
		
		return ret;
	}
}

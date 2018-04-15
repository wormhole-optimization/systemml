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

package org.apache.sysml.api.mlcontext;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.MalformedURLException;
import java.net.URL;

import org.apache.commons.io.FileUtils;
import org.apache.commons.io.IOUtils;
import org.apache.hadoop.fs.FSDataInputStream;
import org.apache.hadoop.fs.FileSystem;
import org.apache.hadoop.fs.Path;
import org.apache.sysml.runtime.io.IOUtilFunctions;

/**
 * Factory for creating DML and PYDML Script objects from strings, files, URLs,
 * and input streams.
 *
 */
public class ScriptFactory {

	/**
	 * Create a DML Script object based on a string path to a file.
	 *
	 * @param scriptFilePath
	 *            path to DML script file (local or HDFS)
	 * @return DML Script object
	 */
	public static Script dmlFromFile(String scriptFilePath) {
		return scriptFromFile(scriptFilePath, ScriptType.DML);
	}

	/**
	 * Create a DML Script object based on an input stream.
	 *
	 * @param inputStream
	 *            input stream to DML
	 * @return DML Script object
	 */
	public static Script dmlFromInputStream(InputStream inputStream) {
		return scriptFromInputStream(inputStream, ScriptType.DML);
	}

	/**
	 * Creates a DML Script object based on a file in the local file system. To
	 * create a DML Script object from a local file or HDFS, please use
	 * {@link #dmlFromFile(String)}.
	 *
	 * @param localScriptFile
	 *            the local DML file
	 * @return DML Script object
	 */
	public static Script dmlFromLocalFile(File localScriptFile) {
		return scriptFromLocalFile(localScriptFile, ScriptType.DML);
	}

	/**
	 * Create a DML Script object based on a string.
	 *
	 * @param scriptString
	 *            string of DML
	 * @return DML Script object
	 */
	public static Script dmlFromString(String scriptString) {
		return scriptFromString(scriptString, ScriptType.DML);
	}

	/**
	 * Create a DML Script object based on a URL path.
	 *
	 * @param scriptUrlPath
	 *            URL path to DML script
	 * @return DML Script object
	 */
	public static Script dmlFromUrl(String scriptUrlPath) {
		return scriptFromUrl(scriptUrlPath, ScriptType.DML);
	}

	/**
	 * Create a DML Script object based on a URL.
	 *
	 * @param scriptUrl
	 *            URL to DML script
	 * @return DML Script object
	 */
	public static Script dmlFromUrl(URL scriptUrl) {
		return scriptFromUrl(scriptUrl, ScriptType.DML);
	}

	/**
	 * Create a DML Script object based on a resource path.
	 *
	 * @param resourcePath
	 *            path to a resource on the classpath
	 * @return DML Script object
	 */
	public static Script dmlFromResource(String resourcePath) {
		return scriptFromResource(resourcePath, ScriptType.DML);
	}

	/**
	 * Create a PYDML Script object based on a string path to a file.
	 *
	 * @param scriptFilePath
	 *            path to PYDML script file (local or HDFS)
	 * @return PYDML Script object
	 */
	public static Script pydmlFromFile(String scriptFilePath) {
		return scriptFromFile(scriptFilePath, ScriptType.PYDML);
	}

	/**
	 * Create a PYDML Script object based on an input stream.
	 *
	 * @param inputStream
	 *            input stream to PYDML
	 * @return PYDML Script object
	 */
	public static Script pydmlFromInputStream(InputStream inputStream) {
		return scriptFromInputStream(inputStream, ScriptType.PYDML);
	}

	/**
	 * Creates a PYDML Script object based on a file in the local file system.
	 * To create a PYDML Script object from a local file or HDFS, please use
	 * {@link #pydmlFromFile(String)}.
	 *
	 * @param localScriptFile
	 *            the local PYDML file
	 * @return PYDML Script object
	 */
	public static Script pydmlFromLocalFile(File localScriptFile) {
		return scriptFromLocalFile(localScriptFile, ScriptType.PYDML);
	}

	/**
	 * Create a PYDML Script object based on a string.
	 *
	 * @param scriptString
	 *            string of PYDML
	 * @return PYDML Script object
	 */
	public static Script pydmlFromString(String scriptString) {
		return scriptFromString(scriptString, ScriptType.PYDML);
	}

	/**
	 * Creat a PYDML Script object based on a URL path.
	 *
	 * @param scriptUrlPath
	 *            URL path to PYDML script
	 * @return PYDML Script object
	 */
	public static Script pydmlFromUrl(String scriptUrlPath) {
		return scriptFromUrl(scriptUrlPath, ScriptType.PYDML);
	}

	/**
	 * Create a PYDML Script object based on a URL.
	 *
	 * @param scriptUrl
	 *            URL to PYDML script
	 * @return PYDML Script object
	 */
	public static Script pydmlFromUrl(URL scriptUrl) {
		return scriptFromUrl(scriptUrl, ScriptType.PYDML);
	}

	/**
	 * Create a PYDML Script object based on a resource path.
	 *
	 * @param resourcePath
	 *            path to a resource on the classpath
	 * @return PYDML Script object
	 */
	public static Script pydmlFromResource(String resourcePath) {
		return scriptFromResource(resourcePath, ScriptType.PYDML);
	}

	/**
	 * Create a DML or PYDML Script object based on a string path to a file.
	 *
	 * @param scriptFilePath
	 *            path to DML or PYDML script file (local or HDFS)
	 * @param scriptType
	 *            {@code ScriptType.DML} or {@code ScriptType.PYDML}
	 * @return DML or PYDML Script object
	 */
	private static Script scriptFromFile(String scriptFilePath, ScriptType scriptType) {
		String scriptString = getScriptStringFromFile(scriptFilePath);
		return scriptFromString(scriptString, scriptType).setName(scriptFilePath);
	}

	/**
	 * Create a DML or PYDML Script object based on an input stream.
	 *
	 * @param inputStream
	 *            input stream to DML or PYDML
	 * @param scriptType
	 *            {@code ScriptType.DML} or {@code ScriptType.PYDML}
	 * @return DML or PYDML Script object
	 */
	private static Script scriptFromInputStream(InputStream inputStream, ScriptType scriptType) {
		String scriptString = getScriptStringFromInputStream(inputStream);
		return scriptFromString(scriptString, scriptType);
	}

	/**
	 * Creates a DML or PYDML Script object based on a file in the local file
	 * system. To create a Script object from a local file or HDFS, please use
	 * {@link scriptFromFile(String, ScriptType)}.
	 *
	 * @param localScriptFile
	 *            The local DML or PYDML file
	 * @param scriptType
	 *            {@code ScriptType.DML} or {@code ScriptType.PYDML}
	 * @return DML or PYDML Script object
	 */
	private static Script scriptFromLocalFile(File localScriptFile, ScriptType scriptType) {
		String scriptString = getScriptStringFromFile(localScriptFile);
		return scriptFromString(scriptString, scriptType).setName(localScriptFile.getName());
	}

	/**
	 * Create a DML or PYDML Script object based on a string.
	 *
	 * @param scriptString
	 *            string of DML or PYDML
	 * @param scriptType
	 *            {@code ScriptType.DML} or {@code ScriptType.PYDML}
	 * @return DML or PYDML Script object
	 */
	private static Script scriptFromString(String scriptString, ScriptType scriptType) {
		return new Script(scriptString, scriptType);
	}

	/**
	 * Creat a DML or PYDML Script object based on a URL path.
	 *
	 * @param scriptUrlPath
	 *            URL path to DML or PYDML script
	 * @param scriptType
	 *            {@code ScriptType.DML} or {@code ScriptType.PYDML}
	 * @return DML or PYDML Script object
	 */
	private static Script scriptFromUrl(String scriptUrlPath, ScriptType scriptType) {
		String scriptString = getScriptStringFromUrl(scriptUrlPath);
		return scriptFromString(scriptString, scriptType).setName(scriptUrlPath);
	}

	/**
	 * Create a DML or PYDML Script object based on a URL.
	 *
	 * @param scriptUrl
	 *            URL to DML or PYDML script
	 * @param scriptType
	 *            {@code ScriptType.DML} or {@code ScriptType.PYDML}
	 * @return DML or PYDML Script object
	 */
	private static Script scriptFromUrl(URL scriptUrl, ScriptType scriptType) {
		String scriptString = getScriptStringFromUrl(scriptUrl);
		return scriptFromString(scriptString, scriptType).setName(scriptUrl.toString());
	}

	/**
	 * Create a DML or PYDML Script object based on a resource path.
	 *
	 * @param resourcePath
	 *            path to a resource on the classpath
	 * @param scriptType
	 *            {@code ScriptType.DML} or {@code ScriptType.PYDML}
	 * @return DML or PYDML Script object
	 */
	private static Script scriptFromResource(String resourcePath, ScriptType scriptType) {
		if (resourcePath == null) {
			return null;
		}
		if (!resourcePath.startsWith("/")) {
			resourcePath = "/" + resourcePath;
		}
		try( InputStream inputStream = ScriptFactory.class.getResourceAsStream(resourcePath) ) {
			return scriptFromInputStream(inputStream, scriptType).setName(resourcePath);
		} catch (Exception e){
			throw new MLContextException("Error trying to read script from resource: "+ resourcePath, e);
		}
	}

	/**
	 * Create a DML Script object based on a string.
	 *
	 * @param scriptString
	 *            string of DML
	 * @return DML Script object
	 */
	public static Script dml(String scriptString) {
		return dmlFromString(scriptString);
	}

	/**
	 * Obtain a script string from a file in the local file system. To obtain a
	 * script string from a file in HDFS, please use
	 * getScriptStringFromFile(String scriptFilePath).
	 *
	 * @param file
	 *            The script file.
	 * @return The script string.
	 * @throws MLContextException
	 *             If a problem occurs reading the script string from the file.
	 */
	private static String getScriptStringFromFile(File file) {
		if (file == null) {
			throw new MLContextException("Script file is null");
		}
		String filePath = file.getPath();
		try {
			return FileUtils.readFileToString(file);
		} catch (IOException e) {
			throw new MLContextException("Error trying to read script string from file: " + filePath, e);
		}
	}

	/**
	 * Obtain a script string from a file.
	 *
	 * @param scriptFilePath
	 *            The file path to the script file (either local file system or
	 *            HDFS)
	 * @return The script string
	 * @throws MLContextException
	 *             If a problem occurs reading the script string from the file
	 */
	private static String getScriptStringFromFile(String scriptFilePath) {
		if (scriptFilePath == null) {
			throw new MLContextException("Script file path is null");
		}
		try {
			if (   scriptFilePath.startsWith("hdfs:") || scriptFilePath.startsWith("gpfs:")
				|| IOUtilFunctions.isObjectStoreFileScheme(new Path(scriptFilePath))) {
				Path path = new Path(scriptFilePath);
				FileSystem fs = IOUtilFunctions.getFileSystem(path);
				try( FSDataInputStream fsdis = fs.open(path) ) {
					return IOUtils.toString(fsdis);
				}
			} else {// from local file system
				File scriptFile = new File(scriptFilePath);
				return FileUtils.readFileToString(scriptFile);
			}
		} catch (IllegalArgumentException | IOException e) {
			throw new MLContextException("Error trying to read script string from file: " + scriptFilePath, e);
		} 
	}

	/**
	 * Obtain a script string from an InputStream.
	 *
	 * @param inputStream
	 *            The InputStream from which to read the script string
	 * @return The script string
	 * @throws MLContextException
	 *             If a problem occurs reading the script string from the URL
	 */
	private static String getScriptStringFromInputStream(InputStream inputStream) {
		if (inputStream == null) {
			throw new MLContextException("InputStream is null");
		}
		try {
			return IOUtils.toString(inputStream);
		} catch (IOException e) {
			throw new MLContextException("Error trying to read script string from InputStream", e);
		}
	}

	/**
	 * Obtain a script string from a URL.
	 *
	 * @param scriptUrlPath
	 *            The URL path to the script file
	 * @return The script string
	 * @throws MLContextException
	 *             If a problem occurs reading the script string from the URL
	 */
	private static String getScriptStringFromUrl(String scriptUrlPath) {
		if (scriptUrlPath == null) {
			throw new MLContextException("Script URL path is null");
		}
		try {
			URL url = new URL(scriptUrlPath);
			return getScriptStringFromUrl(url);
		} catch (MalformedURLException e) {
			throw new MLContextException("Error trying to read script string from URL path: " + scriptUrlPath, e);
		}
	}

	/**
	 * Obtain a script string from a URL.
	 *
	 * @param url
	 *            The script URL
	 * @return The script string
	 * @throws MLContextException
	 *             If a problem occurs reading the script string from the URL
	 */
	private static String getScriptStringFromUrl(URL url) {
		if (url == null) {
			throw new MLContextException("URL is null");
		}
		String urlString = url.toString();
		if ((!urlString.toLowerCase().startsWith("http:")) && (!urlString.toLowerCase().startsWith("https:"))) {
			throw new MLContextException("Currently only reading from http and https URLs is supported");
		}
		try( InputStream is = url.openStream() ) {
			return IOUtils.toString(is);
		} catch (IOException e) {
			throw new MLContextException("Error trying to read script string from URL: " + url, e);
		}
	}

	/**
	 * Create a PYDML script object based on a string.
	 *
	 * @param scriptString
	 *            string of PYDML
	 * @return PYDML Script object
	 */
	public static Script pydml(String scriptString) {
		return pydmlFromString(scriptString);
	}
}

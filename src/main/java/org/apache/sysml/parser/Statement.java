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

package org.apache.sysml.parser;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.Interval;
import org.apache.commons.logging.Log;
import org.apache.commons.logging.LogFactory;

public abstract class Statement implements ParseInfo
{

	
	protected static final Log LOG = LogFactory.getLog(Statement.class.getName());
	
	public static final String OUTPUTSTATEMENT = "WRITE";
					
	// parameter names for seq()
	public static final String SEQ_FROM = "from"; 
	public static final String SEQ_TO   = "to";
	public static final String SEQ_INCR	= "incr";
		
	public static final String SOURCE  	= "source";
	public static final String SETWD 	= "setwd";

	public static final String MATRIX_DATA_TYPE = "matrix";
	public static final String FRAME_DATA_TYPE = "frame";
	public static final String SCALAR_DATA_TYPE = "scalar";
	
	public static final String DOUBLE_VALUE_TYPE = "double";
	public static final String BOOLEAN_VALUE_TYPE = "boolean";
	public static final String INT_VALUE_TYPE = "int";
	public static final String STRING_VALUE_TYPE = "string";
	
	// String constants related to Grouped Aggregate parameters
	public static final String GAGG_TARGET  = "target";
	public static final String GAGG_GROUPS  = "groups";
	public static final String GAGG_WEIGHTS = "weights";
	public static final String GAGG_FN      = "fn";
	public static final String GAGG_FN_SUM      = "sum";
	public static final String GAGG_FN_COUNT    = "count";
	public static final String GAGG_FN_MEAN     = "mean";
	public static final String GAGG_FN_VARIANCE = "variance";
	public static final String GAGG_FN_CM       = "centralmoment";
	public static final String GAGG_FN_CM_ORDER = "order";
	public static final String GAGG_NUM_GROUPS  = "ngroups";
	
	public abstract boolean controlStatement();
	
	public abstract VariableSet variablesRead();
	public abstract VariableSet variablesUpdated();
 
	public abstract void initializeforwardLV(VariableSet activeIn);
	public abstract VariableSet initializebackwardLV(VariableSet lo);
	
	public abstract Statement rewriteStatement(String prefix);
	
	// Used only insider python parser to allow for ignoring newline logic
	private boolean isEmptyNewLineStatement = false;
	public boolean isEmptyNewLineStatement() {
		return isEmptyNewLineStatement;
	}	
	public void setEmptyNewLineStatement(boolean isEmptyNewLineStatement) {
		this.isEmptyNewLineStatement = isEmptyNewLineStatement;
	}
	
	///////////////////////////////////////////////////////////////////////////
	// store exception info + position information for statements
	///////////////////////////////////////////////////////////////////////////
	
	
	private String _filename;
	private int _beginLine, _beginColumn;
	private int _endLine,   _endColumn;
	private String _text;
	
	public void setFilename(String passed)  { _filename = passed;	}
	public void setBeginLine(int passed)    { _beginLine = passed;	}
	public void setBeginColumn(int passed) 	{ _beginColumn = passed;}
	public void setEndLine(int passed) 		{ _endLine = passed;   }
	public void setEndColumn(int passed)	{ _endColumn = passed; }

	/**
	 * Set ParserRuleContext values (begin line, begin column, end line, end
	 * column, and text).
	 *
	 * @param ctx
	 *            the antlr ParserRuleContext
	 */
	public void setCtxValues(ParserRuleContext ctx) {
		setBeginLine(ctx.start.getLine());
		setBeginColumn(ctx.start.getCharPositionInLine());
		setEndLine(ctx.stop.getLine());
		setEndColumn(ctx.stop.getCharPositionInLine());
		// preserve whitespace if possible
		if ((ctx.start != null) && (ctx.stop != null) && (ctx.start.getStartIndex() != -1)
				&& (ctx.stop.getStopIndex() != -1) && (ctx.start.getStartIndex() <= ctx.stop.getStopIndex())
				&& (ctx.start.getInputStream() != null)) {
			String text = ctx.start.getInputStream()
					.getText(Interval.of(ctx.start.getStartIndex(), ctx.stop.getStopIndex()));
			if (text != null) {
				text = text.trim();
			}
			setText(text);
		} else {
			String text = ctx.getText();
			if (text != null) {
				text = text.trim();
			}
			setText(text);
		}
	}

	/**
	 * Set ParserRuleContext values (begin line, begin column, end line, end
	 * column, and text) and file name.
	 *
	 * @param ctx
	 *            the antlr ParserRuleContext
	 * @param filename
	 *            the filename (if it exists)
	 */
	public void setCtxValuesAndFilename(ParserRuleContext ctx, String filename) {
		setCtxValues(ctx);
		setFilename(filename);
	}

	public int getBeginLine()	{ return _beginLine;   }
	public int getBeginColumn() { return _beginColumn; }
	public int getEndLine() 	{ return _endLine;   }
	public int getEndColumn()	{ return _endColumn; }
	public String getFilename() { return _filename;  }

	public String printErrorLocation() {
		String file = _filename;
		if (file == null) {
			file = "";
		} else {
			file = file + " ";
		}
		if (getText() != null) {
			return "ERROR: " + file + "[line " + _beginLine + ":" + _beginColumn + "] -> " + getText() + " -- ";
		} else {
			return "ERROR: " + file + "[line " + _beginLine + ":" + _beginColumn + "] -- ";
		}
	}

	public String printWarningLocation() {
		String file = _filename;
		if (file == null) {
			file = "";
		} else {
			file = file + " ";
		}
		if (getText() != null) {
			return "WARNING: " + file + "[line " + _beginLine + ":" + _beginColumn + "] -> " + getText() + " -- ";
		} else {
			return "WARNING: " + file + "[line " + _beginLine + ":" + _beginColumn + "] -- ";
		}
	}

	public void raiseValidateError(String msg, boolean conditional) {
		raiseValidateError(msg, conditional, null);
	}

	public void raiseValidateError(String msg, boolean conditional, String errorCode) {
		if (conditional) {// warning if conditional
			String fullMsg = this.printWarningLocation() + msg;
			LOG.warn(fullMsg);
		} else {// error and exception if unconditional
			String fullMsg = this.printErrorLocation() + msg;
			if (errorCode != null)
				throw new LanguageException(fullMsg, errorCode);
			else
				throw new LanguageException(fullMsg);
		}
	}

	public String getText() {
		return _text;
	}

	public void setText(String text) {
		this._text = text;
	}

	/**
	 * Set parse information.
	 *
	 * @param parseInfo
	 *            parse information, such as beginning line position, beginning
	 *            column position, ending line position, ending column position,
	 *            text, and filename
	 * @param filename
	 *            the DML/PYDML filename (if it exists)
	 */
	public void setParseInfo(ParseInfo parseInfo) {
		_beginLine = parseInfo.getBeginLine();
		_beginColumn = parseInfo.getBeginColumn();
		_endLine = parseInfo.getEndLine();
		_endColumn = parseInfo.getEndColumn();
		_text = parseInfo.getText();
		_filename = parseInfo.getFilename();
	}

}

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

import java.util.HashMap;

import org.apache.sysml.parser.LanguageException.LanguageErrorCodes;

public abstract class Identifier extends Expression
{
	protected DataType _dataType;
	protected ValueType _valueType;
	protected long _dim1;
	protected long _dim2;
	protected int _rows_in_block;
	protected int _columns_in_block;
	protected long _nnz;
	protected FormatType _formatType;

	public Identifier() {
		_dim1 = -1;
		_dim2 = -1;
		_dataType = DataType.UNKNOWN;
		_valueType = ValueType.UNKNOWN;
		_rows_in_block = -1;
		_columns_in_block = -1;
		_nnz = -1;
		setOutput(this);
		_formatType = null;
	}
	
	public void setProperties(Identifier i) {
		if (i == null) 
			return;
		_dataType = i.getDataType();
		_valueType = i.getValueType();
		if (i instanceof IndexedIdentifier) {
			_dim1 = ((IndexedIdentifier)i).getOrigDim1();
			_dim2 = ((IndexedIdentifier)i).getOrigDim2();
		}
		else {
			_dim1 = i.getDim1();
			_dim2 = i.getDim2();
		}
		_rows_in_block = i.getRowsInBlock();
		_columns_in_block = i.getColumnsInBlock();
		_nnz = i.getNnz();
		_formatType = i.getFormatType();
	}
	
	public void setDimensionValueProperties(Identifier i) {
		if (i instanceof IndexedIdentifier) {
			IndexedIdentifier ixi = (IndexedIdentifier)i; 
			_dim1 = ixi.getOrigDim1();
			_dim2 = ixi.getOrigDim2();
		}
		else {
			_dim1 = i.getDim1();
			_dim2 = i.getDim2();
		}
		_nnz = i.getNnz();
		_dataType = i.getDataType();
		_valueType = i.getValueType();
	}
	
	public void setDataType(DataType dt){
		_dataType = dt;
	}
	
	public void setValueType(ValueType vt){
		_valueType = vt;
	}
	
	public void setFormatType(FormatType ft){
		_formatType = ft;
	}
	
	public void setDimensions(long dim1, long dim2){
		_dim1 = dim1;
		_dim2 = dim2;
	}
		
	public void setBlockDimensions(int dim1, int dim2){
		 _rows_in_block = dim1;
		 _columns_in_block = dim2;
	}
	
	public void setNnz(long nnzs){
		_nnz = nnzs;
	}
	
	public long getDim1(){
		return _dim1;
	}
	
	public long getDim2(){
		return _dim2;
	}
	
	public DataType getDataType(){
		return _dataType;
	}
	
	public ValueType getValueType(){
		return _valueType;
	}
	
	public FormatType getFormatType(){
		return _formatType;
	}
	
	public int getRowsInBlock(){
		return _rows_in_block;
	}
	
	public int getColumnsInBlock(){
		return _columns_in_block;
	}
	
	public long getNnz(){
		return _nnz;
	}
	
	@Override
	public void validateExpression(HashMap<String,DataIdentifier> ids, HashMap<String,ConstIdentifier> constVars, boolean conditional) 
	{
		
		if( getOutput() instanceof DataIdentifier ) {
			
			// set properties for Data identifier
			String name = ((DataIdentifier)this.getOutput()).getName();
			Identifier id = ids.get(name);
			if ( id == null ){
				//undefined variables are always treated unconditionally as error in order to prevent common script-level bugs
				raiseValidateError("Undefined Variable (" + name + ") used in statement", false, LanguageErrorCodes.INVALID_PARAMETERS);
			}
			this.getOutput().setProperties(id);
			
			// validate IndexedIdentifier -- which is substype of DataIdentifer with index
			if (this.getOutput() instanceof IndexedIdentifier){
				
				// validate the row / col index bounds (if defined)
				IndexedIdentifier indexedIdentiferOut = (IndexedIdentifier)this.getOutput();
				
				if (indexedIdentiferOut.getRowLowerBound() != null) {
					indexedIdentiferOut.getRowLowerBound().validateExpression(ids, constVars, conditional);
					
					Expression tempExpr = indexedIdentiferOut.getRowLowerBound(); 
					if (tempExpr.getOutput().getDataType() == Expression.DataType.MATRIX){	
						raiseValidateError("Matrix values for row lower index bound are not supported, which includes indexed identifiers.", conditional);
					}
					
				}
				if (indexedIdentiferOut.getRowUpperBound() != null) {
					indexedIdentiferOut.getRowUpperBound().validateExpression(ids, constVars, conditional);
					
					Expression tempExpr = indexedIdentiferOut.getRowUpperBound(); 
					if (tempExpr.getOutput().getDataType() == Expression.DataType.MATRIX){	
						raiseValidateError("Matrix values for row upper index bound are not supported, which includes indexed identifiers.", conditional);
					}
				
				}
				if (indexedIdentiferOut.getColLowerBound() != null) {
					indexedIdentiferOut.getColLowerBound().validateExpression(ids,constVars, conditional);	
				
					Expression tempExpr = indexedIdentiferOut.getColLowerBound(); 
					if (tempExpr.getOutput().getDataType() == Expression.DataType.MATRIX){	
						raiseValidateError("Matrix values for column lower index bound are not supported, which includes indexed identifiers.", conditional);
					}
				
				}
				if (indexedIdentiferOut.getColUpperBound() != null) {
					indexedIdentiferOut.getColUpperBound().validateExpression(ids, constVars, conditional);
					
					Expression tempExpr = indexedIdentiferOut.getColUpperBound(); 
					if (tempExpr.getOutput().getDataType() == Expression.DataType.MATRIX){	
						raiseValidateError("Matrix values for column upper index bound are not supported, which includes indexed identifiers.", conditional);
					}
				
				}
				
				IndexPair updatedIndices = ((IndexedIdentifier)this.getOutput()).calculateIndexedDimensions(ids, constVars, conditional);
				((IndexedIdentifier)this.getOutput()).setDimensions(updatedIndices._row, updatedIndices._col);
				
			}
							
		} else {
			this.getOutput().setProperties(this.getOutput());
		}
	}
	
	public void computeDataType() {
				
		if ((_dim1 == 0) && (_dim2 == 0)) {
			_dataType = DataType.SCALAR;
		} else if ((_dim1 >= 1) || (_dim2 >= 1)){
			// Vector also set as matrix
			// Data type is set as matrix, if either of dimensions is -1
			_dataType = DataType.MATRIX;
		} else _dataType = DataType.UNKNOWN;	 
		
	}
	
	public void setBooleanProperties(){
		_dataType = DataType.SCALAR;
		_valueType = ValueType.BOOLEAN;
		_dim1 = 0;
		_dim2 = 0;
		_rows_in_block = 0;
		_columns_in_block = 0;
		_nnz = -1;
		_formatType = null;
	}
	
	public void setIntProperties(){
		_dataType = DataType.SCALAR;
		_valueType = ValueType.INT;
		_dim1 = 0;
		_dim2 = 0;
		_rows_in_block = 0;
		_columns_in_block = 0;
		_nnz = -1;
		_formatType = null;
	}
	
	
	public boolean isScalarBoolean(){
		return (_valueType == ValueType.BOOLEAN) && (_dataType == DataType.SCALAR);
	}
	
	public boolean dimsKnown(){
		return ( _dim1 >= 0 && _dim2 >= 0);
	}
}

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

package org.apache.sysml.runtime.transform.encode;

import java.util.Arrays;
import java.util.List;

import org.apache.sysml.parser.Expression.ValueType;
import org.apache.sysml.runtime.matrix.data.FrameBlock;
import org.apache.sysml.runtime.matrix.data.MatrixBlock;

/**
 * Simple composite encoder that applies a list of encoders 
 * in specified order. By implementing the default encoder API
 * it can be used as a drop-in replacement for any other encoder. 
 * 
 */
public class EncoderComposite extends Encoder
{
	private static final long serialVersionUID = -8473768154646831882L;
	
	private List<Encoder> _encoders = null;
	private FrameBlock _meta = null;
	
	protected EncoderComposite(List<Encoder> encoders) {
		super(null, -1);
		_encoders = encoders;
	}

	@Override
	public int getNumCols() {
		int clen = 0;
		for( Encoder encoder : _encoders )
			clen = Math.max(clen, encoder.getNumCols());
		return clen;
	}

	public List<Encoder> getEncoders() {
		return _encoders;
	}
	
	@Override
	public MatrixBlock encode(FrameBlock in, MatrixBlock out) {
		try {
			//build meta data first (for all encoders)
			for( Encoder encoder : _encoders )
				encoder.build(in);
			
			//propagate meta data 
			_meta = new FrameBlock(in.getNumColumns(), ValueType.STRING);
			for( Encoder encoder : _encoders )
				_meta = encoder.getMetaData(_meta);
			for( Encoder encoder : _encoders )
				encoder.initMetaData(_meta);
			
			//apply meta data
			for( Encoder encoder : _encoders )
				out = encoder.apply(in, out);
		}
		catch(Exception ex) {
			LOG.error("Failed transform-encode frame with \n" + this);
			throw ex;
		}
		
		return out;
	}

	@Override
	public void build(FrameBlock in) {
		for( Encoder encoder : _encoders )
			encoder.build(in);
	}
	
	@Override 
	public MatrixBlock apply(FrameBlock in, MatrixBlock out) {
		try {
			for( Encoder encoder : _encoders )
				out = encoder.apply(in, out);
		}
		catch(Exception ex) {
			LOG.error("Failed to transform-apply frame with \n" + this);
			throw ex;
		}
		return out;
	}
	
	@Override
	public FrameBlock getMetaData(FrameBlock out) {
		if( _meta != null )
			return _meta;
		for( Encoder encoder : _encoders )
			encoder.getMetaData(out);
		return out;
	}
	
	@Override
	public void initMetaData(FrameBlock out) {
		for( Encoder encoder : _encoders )
			encoder.initMetaData(out);
	}
	
	@Override
	public MatrixBlock getColMapping(FrameBlock meta, MatrixBlock out) {
		//determine if dummycode encoder exists
		EncoderDummycode dummy = null;
		for( Encoder encoder : _encoders )
			if( encoder instanceof EncoderDummycode )
				dummy = (EncoderDummycode) encoder;
		//computed shifted start positions
		if( dummy != null ) {
			//delete to dummycode encoder
			out = dummy.getColMapping(meta, out);
		}
		//use simple 1-1 mapping
		else {
			for(int i=0; i<out.getNumRows(); i++) {
				out.quickSetValue(i, 0, i+1);
				out.quickSetValue(i, 1, i+1);
				out.quickSetValue(i, 2, i+1);
			}
		}
		
		return out;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("CompositeEncoder("+_encoders.size()+"):\n");
		for( Encoder encoder : _encoders ) {
			sb.append("-- ");
			sb.append(encoder.getClass().getSimpleName());
			sb.append(": ");
			sb.append(Arrays.toString(encoder.getColList()));
			sb.append("\n");
		}
		return sb.toString();
	}
}

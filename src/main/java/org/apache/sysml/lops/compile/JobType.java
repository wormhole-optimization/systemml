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

package org.apache.sysml.lops.compile;

import org.apache.sysml.hops.Hop.FileFormatTypes;
import org.apache.sysml.lops.Lop;
import org.apache.sysml.lops.Data;
import org.apache.sysml.runtime.DMLRuntimeException;


/**
 * This enumeration defines the set of all map-reduce job types. Each job type
 * is associated with following properties:
 * 
 * id - Unique identifier.
 * 
 * name - Job name.
 * 
 * producesIntermediateOutput - set to false if the the job produces an
 * intermediate output that MUST be consumed by subsequent jobs. The
 * intermediate output is NEVER seen by the end user.
 * 
 * emptyInputsAllowed - defines whether or not the job can take an empty input
 * file as an input. Currently, this flag is set to true only for RAND jobs.
 * 
 * allowsSingleShuffleInstruction - set to true if the job allows only a single
 * instruction in the shuffle phase. For example, jobs that perform matrix 
 * multiplication (MMCJ,MMRJ) can perform only one multiplication per job. 
 * Allowing multiple multiplications within a single job complicates 
 * the implementation (due to specialized key-value pairs for each multiplication) 
 * and such a combination can potentially hinder the performance (since these jobs 
 * make use of a lot of memory). Similarly, SORT job can sort a single stream of values.
 * 
 */

public enum JobType 
{
	/* Add new job types to the following list */
	// 				(id, name, 		emptyInputsAllowed, 	allowsSingleShuffleInstruction, 	allowsNoOtherInstructions)
	INVALID			(-1, "INVALID", 		false, 			false, 								false), 
	ANY				(0, "ANY", 				false, 			false, 								false), 
	GMR				(1, "GMR", 				false, 			false, 								false), 
	DATAGEN			(2, "DATAGEN", 			true, 			false, 								false), 
	REBLOCK			(3, "REBLOCK", 			false, 			false, 								false), 
	MMCJ			(4, "MMCJ", 			false, 			true, 								false), 
	MMRJ			(5, "MMRJ", 			false, 			false, 								false), 
	COMBINE			(6, "COMBINE", 			false, 			false, 								true), 
	SORT			(7, "SORT", 			false, 			true, 								true),  	// allows only "InstructionsBeforeSort" and nothing else. 
	CM_COV			(8, "CM_COV", 			false, 			false, 								false),  	// allows only instructions in the mapper 
	GROUPED_AGG		(9, "GROUPED_AGG", 		false, 			false, 								false), 
	//PARTITION		(10, "PARTITION", false, false, true),	// MB: meta learning removed
	DATA_PARTITION	(11, "DATAPARTITION", 	false, 			false, 								true),
	CSV_REBLOCK		(12, "CSV_REBLOCK", 	false, 			false, 								false),
	CSV_WRITE		(13, "CSV_WRITE", 		false, 			false, 								true),
	GMRCELL			(14, "GMRCELL", 		false, 			false, 								false);


	
	private static int maxJobID = -1;
	static {
		for(JobType jt : JobType.values()) 
		{
			if(jt.getId() > maxJobID)
				maxJobID = jt.getId();
		}
	}
	/* Following code should not be edited when adding a new job type */

	private final int id;
	private final String name;
	
	private final boolean emptyInputsAllowed;
	
	private final boolean allowsSingleShuffleInstruction;

	/**
	 * Indicates whether a job can piggyback "other" operations. 
	 * For example, COMBINE job can only piggyback multiple combine operators but can not perform any other operations.
	 */
	private final boolean allowsNoOtherInstructions;
	
	JobType(int id, String name, boolean aei, boolean assi, boolean anoi) {
		this.id = id;
		this.name = name;
		this.emptyInputsAllowed = aei;
		this.allowsSingleShuffleInstruction = assi;
		this.allowsNoOtherInstructions = anoi;
	}

	public int getId() {
		return id;
	}

	public String getName() {
		return name;
	}

/*	public boolean producesIntermediateOutput() {
		return producesIntermediateOutput;
	}
*/
	public boolean areEmptyInputsAllowed() {
		return emptyInputsAllowed;
	}

	public boolean allowsSingleShuffleInstruction() {
		return allowsSingleShuffleInstruction;
	}

	public boolean allowsNoOtherInstructions() {
		return allowsNoOtherInstructions;
	}

	public Lop.Type getShuffleLopType() {
		if ( !allowsSingleShuffleInstruction )
			throw new DMLRuntimeException("Shuffle Lop Type is not defined for a job (" + getName() + ") with allowsSingleShuffleInstruction=false.");
		else {
			if ( getName().equals("MMCJ") )
				return Lop.Type.MMCJ;
			else if ( getName().equals("MMRJ") )
				return Lop.Type.MMRJ;
			else if ( getName().equals("SORT") )
				return Lop.Type.SortKeys;
			else 
				throw new DMLRuntimeException("Shuffle Lop Type is not defined for a job (" + getName() + ") that allows a single shuffle instruction.");
		}
	}
	
	public static JobType findJobTypeFromLop(Lop node) {
		Lop.Type lt = node.getType();
		switch(lt) {
		case DataGen: 		return JobType.DATAGEN;
		
		case ReBlock:		return JobType.REBLOCK;
		
		case Grouping:		return JobType.GMR;
		
		case MMCJ: 			return JobType.MMCJ;
		
		case MMRJ: 			return JobType.MMRJ;
		
		case MMTSJ: 		return JobType.GMR;
		
		case SortKeys: 		return JobType.SORT;
		
		case CentralMoment: 
		case CoVariance: 
							return JobType.CM_COV;
		
		case GroupedAgg:	return JobType.GROUPED_AGG;
		
		case CombineBinary: 			
		case CombineTernary: 			
							return JobType.COMBINE;
		
		case DataPartition:	return JobType.DATA_PARTITION;
		
		case CSVReBlock:	return JobType.CSV_REBLOCK;
		
		case Data:
			/*
			 * Only Write LOPs with external data formats (except MatrixMarket) produce MR Jobs
			 */
			FileFormatTypes fmt = ((Data) node).getFileFormatType();
			return ( fmt == FileFormatTypes.CSV ) ?
				JobType.CSV_WRITE : null;
			
		default:
			return null; 
		}
	}
	
	public boolean isCompatibleWithParentNodes()
	{
		if ( !allowsSingleShuffleInstruction )
			throw new DMLRuntimeException("isCompatibleWithParentNodes() can not be invoked for a job (" + getName() + ") with allowsSingleShuffleInstruction=false.");
		else {
			if ( getName().equals("MMCJ") )
				return false;
			else if ( getName().equals("MMRJ") || getName().equals("SORT"))
				return true;
			else 
				throw new DMLRuntimeException("Implementation for isCompatibleWithParentNodes() is missing for a job (" + getName() + ") that allows a single shuffle instruction.");
		}
	}
	
	public boolean allowsRecordReaderInstructions() {
		return getName().equals("GMR"); 
	}
	
	public int getBase() {
		if (id == -1)
			return 0;
		else if (id == 0) {
			// for ANY, return the bit vector with x number of 1's, 
			//   where x = number of actual job types (i.e., excluding INVALID,ANY)
			return (int) Math.pow(2, maxJobID)-1;
		}
		else 
			return (int) Math.pow(2, id-1);
	}

	public static int getNumJobTypes() {
		return values().length;
	}
}

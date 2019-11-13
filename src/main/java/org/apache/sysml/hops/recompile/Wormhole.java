package org.apache.sysml.hops.recompile;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import org.apache.sysml.api.DMLScript;
import org.apache.sysml.api.DMLScript.RUNTIME_PLATFORM;
import org.apache.sysml.conf.ConfigurationManager;
import org.apache.sysml.hops.AggBinaryOp;
import org.apache.sysml.hops.AggUnaryOp;
import org.apache.sysml.hops.BinaryOp;
import org.apache.sysml.hops.DataGenOp;
import org.apache.sysml.hops.DataOp;
import org.apache.sysml.hops.FunctionOp;
import org.apache.sysml.hops.Hop;
import org.apache.sysml.hops.HopsException;
import org.apache.sysml.hops.Hop.AggOp;
import org.apache.sysml.hops.Hop.DataGenMethod;
import org.apache.sysml.hops.Hop.DataOpTypes;
import org.apache.sysml.hops.Hop.Direction;
import org.apache.sysml.hops.Hop.FileFormatTypes;
import org.apache.sysml.hops.Hop.OpOp1;
import org.apache.sysml.hops.Hop.OpOp2;
import org.apache.sysml.hops.Hop.OpOp3;
import org.apache.sysml.hops.Hop.OpOp4;
import org.apache.sysml.hops.Hop.OpOpN;
import org.apache.sysml.hops.Hop.ReOrgOp;
import org.apache.sysml.hops.IndexingOp;
import org.apache.sysml.hops.LeftIndexingOp;
import org.apache.sysml.hops.LiteralOp;
import org.apache.sysml.hops.NaryOp;
import org.apache.sysml.hops.OptimizerUtils;
import org.apache.sysml.hops.QuaternaryOp;
import org.apache.sysml.hops.ReorgOp;
import org.apache.sysml.hops.TernaryOp;
import org.apache.sysml.hops.UnaryOp;
import org.apache.sysml.parser.DataIdentifier;
import org.apache.sysml.parser.Expression;
import org.apache.sysml.parser.Expression.ValueType;

import scala.Tuple2;

public class Wormhole {
    private final boolean LOG_WARP_STD = ConfigurationManager.isWormholeWarpStdLogEnabled();
    private final boolean LOG_WARP_ERR = ConfigurationManager.isWormholeWarpErrLogEnabled();
    private final boolean LOG_DES = ConfigurationManager.isWormholeDeserializationLogEnabled();
    private final boolean USE_MEGACACHE = ConfigurationManager.isWormholeCacheEnabled();
    private final String HOPS_FOLDER = ConfigurationManager.getWormholeFolder();
    private final boolean HOPS_META = ConfigurationManager.useWormholeMetadata();
    private final boolean MANUAL_OPT = ConfigurationManager.isWormholeManual();

    /**
     * Optimize the HOP DAG via the wormhole optimizer
     * 
     * @param roots The roots of the HOP DAG
     * @return Optimized rooted HOP DAG
     */
    public ArrayList<Hop> optimize(List<Hop> roots) {
        int hc = roots.hashCode();
        String file = HOPS_FOLDER + "/hops_" + hc;

        // HOP cache that is maintained over the entire serde process
        Map<Long, Hop> megaCache = new HashMap<Long, Hop>();

        // Serialize the HOPs
        serialize(roots, megaCache, file);

        try {
            // Execute warp.
            // Send the file into the void, the event horizon, the final frontier,
            // to infinity and beyond!
            // TODO execute system call to warp
            Process p = Runtime.getRuntime().exec("cp " + file + " " + file + "_opt");

            if (LOG_WARP_STD) {
                // Log warp std out
                BufferedReader stdInput = new BufferedReader(new InputStreamReader(p.getInputStream()));
                String stdLog = file + "_log_std";
                Files.deleteIfExists(new File(stdLog).toPath());
                BufferedWriter writerStd = new BufferedWriter(new FileWriter(stdLog, true));
                String strStd;
                while ((strStd = stdInput.readLine()) != null) {
                    writerStd.append(strStd + "\n");
                }
                writerStd.close();
            }

            if (LOG_WARP_ERR) {
                // Log warp err out
                BufferedReader errInput = new BufferedReader(new InputStreamReader(p.getErrorStream()));
                String errLog = file + "_log_err";
                Files.deleteIfExists(new File(errLog).toPath());
                BufferedWriter writerErr = new BufferedWriter(new FileWriter(errLog, true));
                String strErr;
                while ((strErr = errInput.readLine()) != null) {
                    writerErr.append(strErr + "\n");
                }
                writerErr.close();
            }

            // Wait for a certain amount of time for warp to finish before timing out
            p.waitFor(5, TimeUnit.MINUTES);
        } catch (IOException | InterruptedException e) {
            throw new RuntimeException("[ERROR] Exception thrown while executing warp", e);
        }

        // Recover the optimized plan
        ArrayList<Hop> optimized;
        if (MANUAL_OPT) {
            optimized = deserialize(megaCache, "/tmp/hop_test");
        } else {
            optimized = deserialize(megaCache, file + "_opt");
        }

        return optimized;
    }

    /**
     * Deserialize HOPs from a file.
     * 
     * @param megaCache Serde HOP cache
     * @param file The file path to read the HOP DAG information from
     * @return A list of HOP DAG roots
     */
    private ArrayList<Hop> deserialize(Map<Long, Hop> megaCache, String file) {
        try (BufferedReader reader = new BufferedReader(new FileReader(file))) {
            // Register the serialized HOPs
            List<String> dagStrings = new ArrayList<>();
            String line;
            while ((line = reader.readLine()) != null) {
                if (!line.equals("") && !line.equals("\n")) {
                    dagStrings.add(line);
                }
            }

            // Deserialize the HOP DAG and list the roots found
            ArrayList<Hop> roots = new ArrayList<>();
            for (Hop root : deserializeDag(dagStrings, megaCache)) {
                roots.add(root);
            }
            return roots;
        } catch (IOException e) {
            throw new RuntimeException("[ERROR] Exception thrown while parsing HOP file: " + file, e);
        }
    }

    /**
     * Deserialize a list of strings representing a dag. Assume child-first
     * topological order.
     * 
     * @param dagString A list of serialized HOPs that make up a HOP DAG
     * @param megaCache Serde HOP cache
     * @return HOP DAG roots
     */
    private Set<Hop> deserializeDag(List<String> dagString, Map<Long, Hop> megaCache) {
        // Roots for the HOP DAG deserialized so far
        Set<Hop> roots = new HashSet<Hop>();

        // Deserialization cache for HOPs deserialized so far
        Map<Long, Hop> hops = new HashMap<Long, Hop>();

        // Deserialize and cache each hop in the dag
        for (int i = 0; i < dagString.size(); i++) {
            System.out.println(hops.toString());

            Hop hop = deserializeHop(dagString.get(i), hops, megaCache);
            hops.put(hop.getHopID(), hop);

            // Maintain known roots for DAG seen so far
            roots.add(hop);
            for (Hop child : hop.getInput()) {
                roots.remove(child);
            }
        }

        Hop.resetVisitStatus(roots.stream().collect(Collectors.toList()));
        // Refresh row/column block estimates
        for (Hop root : roots) {
            rule_BlockSizeAndReblock(root, ConfigurationManager.getBlocksize());
        }
        Hop.resetVisitStatus(roots.stream().collect(Collectors.toList()));

        // Return the deserialized roots
        return roots;
    }

    /**
     * Deserialize a HOP string.
     * 
     * @param hopString The string encoding the HOP to be deserialized.
     * @param hops      A cache of previously deserialized HOP that could be
     *                  children of the HOP being deserialized.
     * @param megaCache Serde HOP cache
     * @return A HOP object
     */
    private Hop deserializeHop(String hopString, Map<Long, Hop> hops, Map<Long, Hop> megaCache) {
        if (LOG_DES) {
            System.out.println("DESERIALIZE: " + hopString + "\n");
        }

        String[] attributes = hopString.split(";", -1);
        //String lines = attributes[0];
        long hopID = Long.valueOf(attributes[1]);
        Tuple2<String, String> opStrings = firstWordAndRem(attributes[2]);
        String opName = opStrings._1();
        String remainder = opStrings._2();
        List<Long> childrenID = new ArrayList<Long>();
        for (String idString : attributes[3].split(",")) {
            if (!idString.equals("")) {
                childrenID.add(Long.valueOf(idString));
            }
        }
        List<Hop> inp = new ArrayList<Hop>();
        for (long id : childrenID) {
            inp.add(hops.get(id));
        }

        int dim1 = -1;
        int dim2 = -1;
        int rowsInBlock = -1;
        int colsInBlock = -1;
        int nnz = -1;
        if (HOPS_META) {
            List<Integer> matrixCharacteristics = Arrays.asList(attributes[4].split(",")).stream().filter(s -> !s.equals(""))
                .map(s -> Integer.valueOf(s)).collect(Collectors.toList());
            dim1 = matrixCharacteristics.get(0);
            dim2 = matrixCharacteristics.get(1);
            rowsInBlock = matrixCharacteristics.get(2);
            colsInBlock = matrixCharacteristics.get(3);
            nnz = matrixCharacteristics.get(4);
            //String memoryEstimates = attributes[7];
            //String dataFlowProp = attributes[8];
            //String execType = attributes[9];
        }

        Expression.DataType dt = resolveDT(attributes[5]);
        Expression.ValueType vt = resolveVT(attributes[6]);

        // Serde cache lookup first
        if (USE_MEGACACHE) {
            Hop h = null;
            if ((h = megaCache.get(hopID)) != null) {
                // Cache hit, reinitialize the inputs
                h.getInput().clear();
                for (long childID : childrenID) {
                    h.addInput(hops.get(childID));
                }
                return h;
            }
        }

        // New operator found, lets build it!
        Hop h = null;
        if (opName.startsWith("u(") && opName.endsWith(")")) {
            h = new UnaryOp(inp.get(0).getName(), dt, vt, resolveOpOp1(opName), inp.get(0));
        } else if (opName.startsWith("b(") && opName.endsWith(")")) {
            h = new BinaryOp(inp.get(0).getName(), dt, vt, resolveOpOp2(opName), inp.get(0), inp.get(1));
        } else if (opName.startsWith("t(") && opName.endsWith(")")) {
            if (inp.size() == 3) {
                h = new TernaryOp(inp.get(0).getName(), dt, vt, resolveOpOp3(opName), inp.get(0), inp.get(1),
                        inp.get(2));
            } else {
                h = new TernaryOp(inp.get(0).getName(), dt, vt, resolveOpOp3(opName), inp.get(0), inp.get(1),
                        inp.get(2), inp.get(3), inp.get(4));
            }
        } else if (opName.startsWith("q(") && opName.endsWith(")")) {
            h = new QuaternaryOp(inp.get(0).getName(), dt, vt, resolveOpOp4(opName), inp.get(0), inp.get(1),
                    inp.get(2), inp.get(3), true /* post */);
        } else if (opName.startsWith("m(") && opName.endsWith(")")) {
            h = new NaryOp(inp.get(0).getName(), dt, vt, resolveOpOpN(opName), inp.toArray(new Hop[inp.size()]));
        } else if (opName.startsWith("r(") && opName.endsWith(")")) {
            h = new ReorgOp(inp.get(0).getName(), dt, vt, resolveReOrgOp(opName), inp.get(0));
        } else if (opName.startsWith("dg(") && opName.endsWith(")")) {
            h = new DataGenOp(resolveDataGenMethod(opName), new DataIdentifier("dg"),
                resolveInputParamMap(attributes[10], inp));
        } else if (opName.startsWith("LiteralOp")) {
            h = getLiteralOp(vt, opName, remainder);
        } else if (opName.equals(LeftIndexingOp.OPSTRING)) {
            // TODO
            // TODO passedRowsLEU
            // TODO passedColsLEU
            h = new LeftIndexingOp(inp.get(0).getName(), dt, vt, inp.get(0), inp.get(1), inp.get(2), inp.get(3),
                inp.get(4), inp.get(5), true /* passedRowsLEU */, true /* passedColsLEU */);
        } else if (opName.equals(IndexingOp.OPSTRING)) {
            // TODO passedRowsLEU
            // TODO passedColsLEU
            h = new IndexingOp(inp.get(0).getName(), dt, vt, inp.get(0), inp.get(1), inp.get(2), inp.get(3),
                inp.get(4), true /* passedRowsLEU */, true /* passedColsLEU */);
        } else if (opName.equals(FunctionOp.OPSTRING)) {
            // TODO
            throw new IllegalArgumentException("[ERROR] No support for FunctionOp (extfunct)");
        } else if (opName.startsWith("ua(") && opName.endsWith(")")) {
            Tuple2<AggOp, Direction> agg = resolveAgg(opName);
            h = new AggUnaryOp(inp.get(0).getName(), dt, vt, agg._1(), agg._2(), inp.get(0));
        } else if (opName.startsWith("ba(") && opName.endsWith(")")) {
            Tuple2<AggOp, OpOp2> agg = resolveAgg2(opName);
            h = new AggBinaryOp(inp.get(0).getName(), dt, vt, agg._2(), agg._1(), inp.get(0), inp.get(1));
        } else if (opName.startsWith("PRead")) {
            // DataOp
            // h = new DataOp(remainder, dt, vt, DataOpTypes.PERSISTENTREAD, resolveInputParamMap(attributes[10], inp));
            h = new DataOp(remainder, dt, vt, DataOpTypes.PERSISTENTREAD, remainder, dim1, dim2, nnz, rowsInBlock, colsInBlock);
        } else if (opName.startsWith("PWrite")) {
            // DataOp
            // TODO PERSISTENTWRITE
            // h = new DataOp(remainder, dt, vt, Hop.DataOpTypes.TRANSIENTWRITE, inp.get(0), resolveInputParamMap(attributes[10], inp));
            h = new DataOp(remainder, dt, vt, inp.get(0), Hop.DataOpTypes.TRANSIENTWRITE, remainder);
        } else if (opName.startsWith("TRead")) {
            // DataOp
            // h = new DataOp(remainder, dt, vt, DataOpTypes.TRANSIENTREAD, resolveInputParamMap(attributes[10], inp));
            h = new DataOp(remainder, dt, vt, DataOpTypes.TRANSIENTREAD, remainder, dim1, dim2, nnz, rowsInBlock, colsInBlock);
        } else if (opName.startsWith("TWrite")) {
            // DataOp
            // h = new DataOp(remainder, dt, vt, Hop.DataOpTypes.TRANSIENTWRITE, inp.get(0), resolveInputParamMap(attributes[10], inp));
            h = new DataOp(remainder, dt, vt, inp.get(0), Hop.DataOpTypes.TRANSIENTWRITE, remainder);
        } else {
            throw new IllegalArgumentException("[ERROR] Cannot Recognize HOP in string: " + opName);
        }
        h.setHopID(hopID);

        return h;
    }

    /**
     * Serialize a list of hops into child-first topological order.
     * 
     * @param roots     A list of HOP DAG roots 
     * @param megaCache Serde HOP cache 
     * @param file      The file path to write the HOP DAG information from
     */
    private void serialize(List<Hop> roots, Map<Long, Hop> megaCache, String file) {
        try {
            Files.deleteIfExists(new File(file).toPath());

            BufferedWriter writer = new BufferedWriter(new FileWriter(file, true));
            StringBuilder sb = new StringBuilder();
            for (Hop hop : roots) {
                sb.append(serializeHop(hop, new ArrayList<>(), megaCache).toString());
            }
            for (Hop hop : roots) {
                hop.resetVisitStatus();
            }
            writer.append(sb.toString() + "\n");
            writer.close();
        } catch (IOException ex) {
            System.err.println(ex.getStackTrace());
        }
    }

    /**
     * Serialize a HOP if it is in lines. Serializing a hop will serialize its
     * children first.
     * 
     * @param hop   The HOP to serialize
     * @param lines The valid lines to serialize
     * @return The string representation of the HOP and its HOP children in
     *         child-first topological order
     */
    private String serializeHop(Hop hop, ArrayList<Integer> lines, Map<Long, Hop> megaCache) {
        StringBuilder sb = new StringBuilder();

        // Hop already explored, return out
        if (hop.isVisited()) {
            return sb.toString();
        }

        if (USE_MEGACACHE) {
            megaCache.put(hop.getHopID(), hop);
        }

        // Enforce serializing children first
        for (Hop input : hop.getInput()) {
            sb.append(serializeHop(input, lines, megaCache));
        }

        // Serialize this node
        if (isInRange(hop, lines)) {
            // Line bounds
            sb.append("" + hop.getBeginLine() + "," + hop.getEndLine() + ";");

            // HOP ID
            sb.append("" + hop.getHopID() + ";");

            // Operator String
            sb.append(hop.getOpString() + ";");

            // Child(ren) HOP ID(s)
            StringBuilder childs = new StringBuilder();
            boolean childAdded = false;
            for (Hop input : hop.getInput()) {
                childs.append(childAdded ? "," : "");
                childs.append(input.getHopID());
                childAdded = true;
            }
            sb.append(childs.toString() + ";");

            if (HOPS_META) {
                // Matrix characteristics
                sb.append("" + hop.getDim1() + "," + hop.getDim2() + "," + hop.getRowsInBlock() + "," + hop.getColsInBlock() + "," + hop.getNnz());
                if (hop.getUpdateType().isInPlace())
                    sb.append("," + hop.getUpdateType().toString().toLowerCase());
            }
            sb.append(";");

            sb.append(hop.getDataType().name().charAt(0) + ";");

            sb.append(hop.getValueType().name().charAt(0) + ";");

            if (HOPS_META) {
                // memory estimates
                sb.append(showMem(hop.getInputMemEstimate(), false) + ",")
                        .append(showMem(hop.getIntermediateMemEstimate(), false) + ",")
                        .append(showMem(hop.getOutputMemEstimate(), false) + ",")
                        .append(showMem(hop.getMemEstimate(), false));
            }
            sb.append(";");

            if (HOPS_META) {
                // data flow properties
                if (hop.requiresReblock() && hop.requiresCheckpoint())
                    sb.append("rblk,chkpt");
                else if (hop.requiresReblock())
                    sb.append("rblk");
                else if (hop.requiresCheckpoint())
                    sb.append("chkpt");
            }
            sb.append(";");

            if (HOPS_META) {
                // exec type
                if (hop.getExecType() != null) {
                    sb.append(hop.getExecType());
                }
            }
            sb.append(";");

            // Input parameters (if applicable)
            if (hop instanceof DataGenOp) {
                boolean foundParams = false;
                DataGenOp dgOp = (DataGenOp) hop;
                ArrayList<Hop> inputs = dgOp.getInput();
                for (Map.Entry<String, Integer> e : dgOp.getParamIndexMap().entrySet()) {
                    sb.append("" + e.getKey() + ":" + inputs.get(e.getValue()).getHopID() + ",");
                    foundParams = true;
                }
                if (foundParams) {
                    sb.delete(sb.length() - 1, sb.length());
                }
            }
            if (hop instanceof DataOp) {
                boolean foundParams = false;
                DataOp dOp = (DataOp) hop;
                ArrayList<Hop> inputs = dOp.getInput();
                for (Map.Entry<String, Integer> e : dOp.getParamIndexMap().entrySet()) {
                    sb.append("" + e.getKey() + ":" + inputs.get(e.getValue()).getHopID() + ",");
                    foundParams = true;
                }
                if (foundParams) {
                    sb.delete(sb.length() - 1, sb.length());
                }
            }
            sb.append(";");

            sb.append('\n');
        }

        hop.setVisited();
        return sb.toString();
    }

    private HashMap<String, Hop> resolveInputParamMap(String mapString, List<Hop> inp) {
        HashMap<String, Hop> out = new HashMap<String, Hop>();
        String[] entries = mapString.split(",");
        for (String e : entries) {
            String[] pair = e.split(":");
            Long inputID = Long.valueOf(pair[1]);
            Optional<Hop> input = inp.stream().filter(h -> h.getHopID() == inputID).findFirst();
            if (!input.isPresent()) {
                throw new IllegalArgumentException("[ERROR] could not find HOP with ID: " + inputID);
            }
            out.put(pair[0], input.get());
        }
        return out;
    }

    private Hop getLiteralOp(ValueType vt, String opName, String remainder) {
        switch (vt) {
        case INT:
            return new LiteralOp(Long.valueOf(remainder));
        case DOUBLE:
            return new LiteralOp(Double.valueOf(remainder));
        case STRING:
            return new LiteralOp(remainder);
        case BOOLEAN:
            return new LiteralOp(Boolean.valueOf(remainder));
        default:
            throw new IllegalArgumentException("[ERROR] LiteralOp ValueType not recognized: " + remainder);
        }
    }

    private Tuple2<AggOp, OpOp2> resolveAgg2(String opName) {
        opName = opName.substring(3, opName.length() - 1);
        for (Map.Entry<AggOp, String> outerOp : Hop.HopsAgg2String.entrySet()) {
            String outerOpString = outerOp.getValue();
            if (opName.startsWith(outerOpString)) {
                String opNameTail = opName.substring(outerOpString.length());
                for (Map.Entry<OpOp2, String> innerOp : Hop.HopsOpOp2String.entrySet()) {
                    String innerOpString = innerOp.getValue();
                    if (opNameTail.equals(innerOpString)) {
                        return new Tuple2<AggOp, OpOp2>(outerOp.getKey(), innerOp.getKey());
                    }
                }
            }
        }
        throw new IllegalArgumentException("[ERROR] Unrecognized binary aggregation: " + opName);
    }

    private Tuple2<AggOp, Direction> resolveAgg(String opName) {
        opName = opName.substring(3, opName.length() - 1);
        if (opName.endsWith("RC")) {
            AggOp agg = resolveAggOp(opName.substring(0, opName.length() - 2));
            return new Tuple2<AggOp, Direction>(agg, Direction.RowCol);
        } else if (opName.endsWith("R")) {
            AggOp agg = resolveAggOp(opName.substring(0, opName.length() - 1));
            return new Tuple2<AggOp, Direction>(agg, Direction.Row);
        } else if (opName.endsWith("C")) {
            AggOp agg = resolveAggOp(opName.substring(0, opName.length() - 1));
            return new Tuple2<AggOp, Direction>(agg, Direction.Col);
        } else {
            throw new IllegalArgumentException("[ERROR] Unrecognized unary aggregation: " + opName);
        }
    }

    private DataGenMethod resolveDataGenMethod(String opName) {
        return Hop.DataGenMethod.valueOf(opName.substring(3, opName.length() - 1).toUpperCase());
    }

    private AggOp resolveAggOp(String opName) {
        for (Map.Entry<AggOp, String> e : Hop.HopsAgg2String.entrySet()) {
            if (e.getValue().equals(opName)) {
                return e.getKey();
            }
        }
        for (Hop.AggOp op : Hop.AggOp.class.getEnumConstants()) {
            if (op.name().toLowerCase().equals(opName)) {
                return op;
            }
        }
        throw new IllegalArgumentException("[ERROR] Unrecognized AggOp: " + opName);
    }

    private ReOrgOp resolveReOrgOp(String opName) {
        opName = opName.substring(2, opName.length() - 1);
        for (Map.Entry<ReOrgOp, String> e : Hop.HopsTransf2String.entrySet()) {
            if (e.getValue().equals(opName)) {
                return e.getKey();
            }
        }
        for (Hop.ReOrgOp op : Hop.ReOrgOp.class.getEnumConstants()) {
            if (op.name().toLowerCase().equals(opName)) {
                return op;
            }
        }
        throw new IllegalArgumentException("[ERROR] Unrecognized ReOrgOp: " + opName);
    }

    private OpOpN resolveOpOpN(String opName) {
        opName = opName.substring(2, opName.length() - 1);
        for (Hop.OpOpN op : Hop.OpOpN.class.getEnumConstants()) {
            if (op.name().toLowerCase().equals(opName)) {
                return op;
            }
        }
        throw new IllegalArgumentException("[ERROR] Unrecognized OpOpN: " + opName);
    }

    private OpOp4 resolveOpOp4(String opName) {
        opName = opName.substring(2, opName.length() - 1);
        for (Hop.OpOp4 op : Hop.OpOp4.class.getEnumConstants()) {
            if (op.name().toLowerCase().equals(opName)) {
                return op;
            }
        }
        throw new IllegalArgumentException("[ERROR] Unrecognized OpOp4: " + opName);
    }

    private OpOp3 resolveOpOp3(String opName) {
        opName = opName.substring(2, opName.length() - 1);
        for (Map.Entry<Hop.OpOp3, String> e : Hop.HopsOpOp3String.entrySet()) {
            if (e.getValue().equals(opName)) {
                return e.getKey();
            }
        }
        for (Hop.OpOp3 op : Hop.OpOp3.class.getEnumConstants()) {
            if (op.name().toLowerCase().equals(opName)) {
                return op;
            }
        }
        throw new IllegalArgumentException("[ERROR] Unrecognized OpOp3: " + opName);
    }

    private OpOp2 resolveOpOp2(String opName) {
        opName = opName.substring(2, opName.length() - 1);
        for (Map.Entry<Hop.OpOp2, String> e : Hop.HopsOpOp2String.entrySet()) {
            if (e.getValue().equals(opName)) {
                return e.getKey();
            }
        }
        for (Hop.OpOp2 op : Hop.OpOp2.class.getEnumConstants()) {
            if (op.name().toLowerCase().equals(opName)) {
                return op;
            }
        }
        throw new IllegalArgumentException("[ERROR] Unrecognized OpOp2: " + opName);
    }

    private OpOp1 resolveOpOp1(String opName) {
        opName = opName.substring(2, opName.length() - 1);
        for (Map.Entry<Hop.OpOp1, String> e : Hop.HopsOpOp12String.entrySet()) {
            if (e.getValue().equals(opName)) {
                return e.getKey();
            }
        }
        for (Hop.OpOp1 op : Hop.OpOp1.class.getEnumConstants()) {
            if (op.name().toLowerCase().equals(opName)) {
                return op;
            }
        }
        throw new IllegalArgumentException("[ERROR] Unrecognized OpOp1: " + opName);
    }

    private ValueType resolveVT(String s) {
        switch (s) {
        case "D":
            return Expression.ValueType.DOUBLE;
        case "I":
            return Expression.ValueType.INT;
        case "B":
            return Expression.ValueType.BOOLEAN;
        case "S":
            return Expression.ValueType.STRING;
        case "O":
            return Expression.ValueType.OBJECT;
        case "U":
            return Expression.ValueType.UNKNOWN;
        default:
            throw new IllegalArgumentException("[ERROR] Unrecognized ValueType: " + s);
        }
    }

    private Expression.DataType resolveDT(String s) {
        switch (s) {
        case "M":
            return Expression.DataType.MATRIX;
        case "S":
            return Expression.DataType.SCALAR;
        case "F":
            return Expression.DataType.FRAME;
        case "O":
            return Expression.DataType.OBJECT;
        case "U":
            return Expression.DataType.UNKNOWN;
        default:
            throw new IllegalArgumentException("[ERROR] Unrecognized DataType: " + s);
        }
    }

    // From Explain.java
    private boolean isInRange(Hop hop, ArrayList<Integer> lines) {
        boolean isInRange = lines.size() == 0;
        for (int lineNum : lines) {
            if (hop.getBeginLine() == lineNum && lineNum == hop.getEndLine()) {
                return true;
            }
        }
        return isInRange;
    }

    // From Explain.java
    private String showMem(double mem, boolean units) {
        if (mem >= OptimizerUtils.DEFAULT_SIZE) {
            return "MAX";
        }
        return OptimizerUtils.toMB(mem) + (units ? "MB" : "");
    }

    // From ParseExplain.kt
    private Tuple2<String, String> firstWordAndRem(String str) {
        int idx = str.indexOf(' ');
        if( idx == -1 ) {
            return new Tuple2<>(str, null);
        } else {
            return new Tuple2<>(str.substring(0, idx), str.substring(idx+1));
        }
    }

    private void rule_BlockSizeAndReblock(Hop hop, final int blocksize) 
	{
		// Go to the source(s) of the DAG
		for (Hop hi : hop.getInput()) {
			if (!hi.isVisited())
				rule_BlockSizeAndReblock(hi, blocksize);
		}

		boolean canReblock = isReblockValid();
		
		if (hop instanceof DataOp) 
		{
			DataOp dop = (DataOp) hop;
			
			// if block size does not match
			if( canReblock && 
				( (dop.getDataType() == Expression.DataType.MATRIX && (dop.getRowsInBlock() != blocksize || dop.getColsInBlock() != blocksize))
				||(dop.getDataType() == Expression.DataType.FRAME && OptimizerUtils.isSparkExecutionMode() && (dop.getInputFormatType()==FileFormatTypes.TEXT
						  || dop.getInputFormatType()==FileFormatTypes.CSV))) ) 
			{
				if( dop.getDataOpType() == DataOp.DataOpTypes.PERSISTENTREAD) 
				{
					// insert reblock after the hop
					dop.setRequiresReblock(true);
					dop.setOutputBlocksizes(blocksize, blocksize);
				} 
				else if( dop.getDataOpType() == DataOp.DataOpTypes.PERSISTENTWRITE ) 
				{
					if (dop.getRowsInBlock() == -1 && dop.getColsInBlock() == -1) 
					{
						// if this dataop is for cell output, then no reblock is needed 
						// as (A) all jobtypes can produce block2cell and cell2cell and 
						// (B) we don't generate an explicit instruction for it (the info 
						// is conveyed through OutputInfo.
					} 
					else if (dop.getInput().get(0).requiresReblock() && dop.getInput().get(0).getParent().size() == 1) 
					{
						// if a reblock is feeding into this, then use it if this is
						// the only parent, otherwise new Reblock
						dop.getInput().get(0).setOutputBlocksizes(dop.getRowsInBlock(),dop.getColsInBlock());
					} 
					else 
					{
						// insert reblock after the hop
						dop.setRequiresReblock(true);
						dop.setOutputBlocksizes(blocksize, blocksize);
					}
				} 
				else if (dop.getDataOpType() == DataOp.DataOpTypes.TRANSIENTWRITE
						|| dop.getDataOpType() == DataOp.DataOpTypes.TRANSIENTREAD) {
					if ( DMLScript.rtplatform == RUNTIME_PLATFORM.SINGLE_NODE ) {
						// simply copy the values from its input
						dop.setRowsInBlock(hop.getInput().get(0).getRowsInBlock());
						dop.setColsInBlock(hop.getInput().get(0).getColsInBlock());
					}
					else {
						// by default, all transient reads and writes are in blocked format
						dop.setRowsInBlock(blocksize);
						dop.setColsInBlock(blocksize);
					}

				} else {
					throw new HopsException(hop.printErrorLocation() + "unexpected non-scalar Data HOP in reblock.\n");
				}
			}
		} 
		else //NO DATAOP 
		{
			// TODO: following two lines are commented, and the subsequent hack is used instead!
			//set_rows_per_block(GLOBAL_BLOCKSIZE);
			//set_cols_per_block(GLOBAL_BLOCKSIZE);
			
			/*
			 * Handle hops whose output dimensions are unknown!
			 * 
			 * Constraint C1:
			 * Currently, only ctable() and groupedAggregate() fall into this category.
			 * The MR jobs for both these functions run in "cell" mode and hence make their
			 * blocking dimensions to (-1,-1).
			 * 
			 * Constraint C2:
			 * Blocking dimensions are not applicable for hops that produce scalars. 
			 * CMCOV and GroupedAgg jobs always run in "cell" mode, and hence they 
			 * produce output in cell format.
			 * 
			 * Constraint C3:
			 * Remaining hops will get their blocking dimensions from their input hops.
			 */
			
			if ( hop.requiresReblock() ) {
				hop.setRowsInBlock(blocksize);
				hop.setColsInBlock(blocksize);
			}
			
			// Constraint C1:
			
			// Constraint C2:
			else if ( hop.getDataType() == Expression.DataType.SCALAR ) {
				hop.setRowsInBlock(-1);
				hop.setColsInBlock(-1);
			}

			// Constraint C3:
			else {
				if ( !canReblock ) {
					hop.setRowsInBlock(-1);
					hop.setColsInBlock(-1);
				}
				else {
					hop.setRowsInBlock(blocksize);
					hop.setColsInBlock(blocksize);
					
					// Functions may return multiple outputs, as defined in array of outputs in FunctionOp.
					// Reblock properties need to be set for each output.
					if ( hop instanceof FunctionOp ) {
						FunctionOp fop = (FunctionOp) hop;
						if ( fop.getOutputs() != null) {
							for(Hop out : fop.getOutputs()) {
								out.setRowsInBlock(blocksize);
								out.setColsInBlock(blocksize);
							}
						}
					}
				}
				
				// if any input is not blocked then the output of current Hop should not be blocked
				for ( Hop h : hop.getInput() ) {
					if ( h.getDataType() == Expression.DataType.MATRIX && h.getRowsInBlock() == -1 && h.getColsInBlock() == -1 ) {
						hop.setRowsInBlock(-1);
						hop.setColsInBlock(-1);
						break;
					}
				}
			}
		}

		hop.setVisited();
    }
    
    private static boolean isReblockValid() {
		return ( DMLScript.rtplatform != RUNTIME_PLATFORM.SINGLE_NODE);
	}
}

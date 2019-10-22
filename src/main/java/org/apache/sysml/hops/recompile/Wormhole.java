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

import org.apache.sysml.conf.ConfigurationManager;
import org.apache.sysml.hops.AggBinaryOp;
import org.apache.sysml.hops.AggUnaryOp;
import org.apache.sysml.hops.BinaryOp;
import org.apache.sysml.hops.DataGenOp;
import org.apache.sysml.hops.FunctionOp;
import org.apache.sysml.hops.Hop;
import org.apache.sysml.hops.Hop.AggOp;
import org.apache.sysml.hops.Hop.DataGenMethod;
import org.apache.sysml.hops.Hop.Direction;
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
    private static final boolean DEBUG = false;
    private static final String HOPS = "/tmp/hops";

    /**
     * Optimize the HOP DAGS via the wormhole optimizer
     * 
     * @param roots The roots of the HOP DAGs
     * @return Optimized rooted HOP DAGs
     */
    public static ArrayList<Hop> optimize(List<Hop> roots) {
        int hc = roots.hashCode();
        String file = HOPS + "_" + hc;

        // Hop cache
        Map<Long, Hop> megaCache = new HashMap<Long, Hop>();

        // Serialize the HOPS
        serialize(roots, megaCache, file);

        // Send the file into the void, the event horizon, the final frontier, to
        // infinity and beyond!
        try {
            if (ConfigurationManager.isWormholeEnabled()) {
                Process p = Runtime.getRuntime().exec("echo NO OPTIMIZATION");
                if (DEBUG) {
                    BufferedReader stdInput = new BufferedReader(new InputStreamReader(p.getInputStream()));
                    BufferedReader stdError = new BufferedReader(new InputStreamReader(p.getErrorStream()));
                    String str;
                    while ((str = stdInput.readLine()) != null) {
                        System.out.println(str);
                        // TODO log
                    }
                    while ((str = stdError.readLine()) != null) {
                        System.err.println(str);
                        // TODO log
                    }
                }
                p.waitFor(5, TimeUnit.MINUTES);
            }
        } catch (IOException | InterruptedException e) {
            System.err.println("Error executing warp");
        }

        ArrayList<Hop> optimized = deserialize(megaCache, file);

        serialize(optimized, megaCache, file + "_serdeser");

        return optimized;
    }

    /**
     * Deserialize hops from a file.
     * 
     * @return A list of HOP DAG roots
     */
    private static ArrayList<Hop> deserialize(Map<Long, Hop> megaCache, String file) {
        try {
            BufferedReader reader = new BufferedReader(new FileReader(file));
            ArrayList<Hop> roots = new ArrayList<>();
            List<String> dagString = new ArrayList<>();
            Map<Long, Hop> hops = new HashMap<Long, Hop>();
            String line;
            while ((line = reader.readLine()) != null) {
                if ((line.equals("") || line.equals("\n")) && dagString.size() != 0) {
                    for (Hop root : deserializeDag(dagString, hops, megaCache)) {
                        roots.add(root);
                    }
                    dagString.clear();
                } else {
                    dagString.add(line);
                }
            }
            reader.close();
            return roots;
        } catch (IOException e) {
            System.err.println(e.getStackTrace());
        }

        return null;
    }

    /**
     * Deserialize a list of strings representing a dag. Assume child-first
     * topological order
     * 
     * @param dagString A list of serialized HOPs that make up a HOP DAG
     * @return A HOP DAG root
     */
    private static Set<Hop> deserializeDag(List<String> dagString, Map<Long, Hop> hops, Map<Long, Hop> megaCache) {
        // Deserialize and cache each hop in the dag
        Set<Hop> roots = new HashSet<Hop>();
        for (int i = 0; i < dagString.size(); i++) {
            Hop hop = deserializeHop(dagString.get(i), hops, megaCache);
            hops.put(hop.getHopID(), hop);
            roots.add(hop);
            for (Hop child : hop.getInput()) {
                roots.remove(child);
            }
        }
        // Return the deserialized roots
        return roots;
    }

    /**
     * Return a deserialized HOP given the serialized HOP string and a cache of
     * potential HOP children
     * 
     * @param hopString The string encoding the HOP to be deserialized
     * @param hops      A cache of previously deserialized HOP that could be
     *                  children of the HOP being deserialized
     * @return A newly constructed HOP
     */
    private static Hop deserializeHop(String hopString, Map<Long, Hop> hops, Map<Long, Hop> megaCache) {

        System.out.println("DESERIALIZE\n********************");
        System.out.println(hopString);

        String[] attributes = hopString.split(";", -1);

        String lines = attributes[0];
        System.out.println(lines);

        long hopID = Long.valueOf(attributes[1]);
        System.out.println(hopID);

        String opName = attributes[2];
        System.out.println(opName);

        List<Long> childrenID = Arrays.asList(attributes[3].split(",")).stream().filter(s -> !s.equals(""))
                .map(s -> Long.valueOf(s)).collect(Collectors.toList());
        System.out.println(childrenID);

        List<Long> matrixCharacteristics = Arrays.asList(attributes[4].split(",")).stream().filter(s -> !s.equals(""))
                .map(s -> Long.valueOf(s)).collect(Collectors.toList());
        System.out.println(matrixCharacteristics);

        Expression.DataType dt = resolveDT(attributes[5]);
        System.out.println(dt.name());

        Expression.ValueType vt = resolveVT(attributes[6]);
        System.out.println(vt.name());

        String memoryEstimates = attributes[7];
        System.out.println(memoryEstimates);

        String dataFlowProp = attributes[8];
        System.out.println(dataFlowProp);

        String execType = attributes[9];
        System.out.println(execType);

        System.out.println("********************");

        // Resolve children as inp
        List<Hop> inp = hops.entrySet().stream().filter(e -> childrenID.contains(e.getKey())).map(e -> e.getValue())
                .collect(Collectors.toList());

        // Cache lookup first
        Hop h = null;
        if ((h = megaCache.get(hopID)) != null) {
            h.getInput().clear();
            for (long childID : childrenID) {
                h.addInput(hops.get(childID));
            }
            return h;
        }

        // New operator found, lets build it!
        if (opName.startsWith("u(") && opName.endsWith(")")) {
            // UnaryOp
            return new UnaryOp(inp.get(0).getName(), dt, vt, resolveOpOp1(opName), inp.get(0));
        } else if (opName.startsWith("b(") && opName.endsWith(")")) {
            // BinaryOp
            return new BinaryOp(inp.get(0).getName(), dt, vt, resolveOpOp2(opName), inp.get(0), inp.get(1));
        } else if (opName.startsWith("t(") && opName.endsWith(")")) {
            // TernaryOp
            if (inp.size() == 3) {
                return new TernaryOp(inp.get(0).getName(), dt, vt, resolveOpOp3(opName), inp.get(0), inp.get(1),
                        inp.get(2));
            } else {
                return new TernaryOp(inp.get(0).getName(), dt, vt, resolveOpOp3(opName), inp.get(0), inp.get(1),
                        inp.get(2), inp.get(3), inp.get(4));
            }
        } else if (opName.startsWith("q(") && opName.endsWith(")")) {
            // QuaternaryOp
            return new QuaternaryOp(inp.get(0).getName(), dt, vt, resolveOpOp4(opName), inp.get(0), inp.get(1),
                    inp.get(2), inp.get(3), true /* post */);
        } else if (opName.startsWith("m(") && opName.endsWith(")")) {
            // NaryOp
            return new NaryOp(inp.get(0).getName(), dt, vt, resolveOpOpN(opName), inp.toArray(new Hop[inp.size()]));
        } else if (opName.startsWith("r(") && opName.endsWith(")")) {
            // ReorgOp
            return new ReorgOp(inp.get(0).getName(), dt, vt, resolveReOrgOp(opName), inp.get(0));
        } else if (opName.startsWith("dg(") && opName.endsWith(")")) {
            // DataGenOp
            return new DataGenOp(resolveDataGenMethod(opName), new DataIdentifier("dg"),
                    resolveDGInputParam(attributes[10], inp));
        } else if (opName.startsWith("LiteralOp ")) {
            // LiteralOp
            return getLiteralOp(vt, opName);
        } else if (opName.equals(LeftIndexingOp.OPSTRING)) {
            // LeftIndexingOp
            // TODO
            throw new IllegalArgumentException("[ERROR] No support for LeftIndexingOp (lix)");
        } else if (opName.equals(IndexingOp.OPSTRING)) {
            // IndexingOp
            // TODO passedRowsLEU
            // TODO passedColsLEU
            return new IndexingOp(inp.get(0).getName(), dt, vt, inp.get(0), inp.get(1), inp.get(2), inp.get(3),
                    inp.get(4), true /* passedRowsLEU */, true /* passedColsLEU */);
        } else if (opName.equals(FunctionOp.OPSTRING)) {
            // FunctionOp
            // TODO
            throw new IllegalArgumentException("[ERROR] No support for FunctionOp (extfunct)");
        } else if (opName.startsWith("ua(") && opName.endsWith(")")) {
            // UnaryAggregateOp
            Tuple2<AggOp, Direction> agg = resolveAgg(opName);
            return new AggUnaryOp(inp.get(0).getName(), dt, vt, agg._1(), agg._2(), inp.get(0));
        } else if (opName.startsWith("ba(") && opName.endsWith(")")) {
            // BinaryAggregateOp
            Tuple2<AggOp, OpOp2> agg = resolveAgg2(opName);
            return new AggBinaryOp(inp.get(0).getName(), dt, vt, agg._2(), agg._1(), inp.get(0), inp.get(1));
        } else if (opName.startsWith("PRead")) {
            // DataOp
            // TODO
            throw new IllegalArgumentException("[ERROR] No support for PRead");
        } else if (opName.startsWith("PWrite")) {
            // DataOp
            // TODO
            throw new IllegalArgumentException("[ERROR] No support for PWrite");
        } else if (opName.startsWith("TRead")) {
            // DataOp
            // TODO
            throw new IllegalArgumentException("[ERROR] No support for TRead");
        } else if (opName.startsWith("TWrite")) {
            // DataOp
            // TODO
            throw new IllegalArgumentException("[ERROR] No support for TWrite");
        }
        throw new IllegalArgumentException("[ERROR] Cannot Recognize HOP in string: " + opName);
    }

    private static HashMap<String, Hop> resolveDGInputParam(String string, List<Hop> inp) {
        HashMap<String, Hop> out = new HashMap<String, Hop>();
        String[] entries = string.split(",");
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

    private static Hop getLiteralOp(ValueType vt, String opName) {
        String valueString = opName.substring("LiteralOp ".length());
        switch (vt) {
        case INT:
            return new LiteralOp(Long.valueOf(valueString));
        case DOUBLE:
            return new LiteralOp(Double.valueOf(valueString));
        case STRING:
            return new LiteralOp(valueString);
        case BOOLEAN:
            return new LiteralOp(Boolean.valueOf(valueString));
        default:
            throw new IllegalArgumentException("[ERROR] LiteralOp ValueType not recognized: " + valueString);
        }
    }

    private static Tuple2<AggOp, OpOp2> resolveAgg2(String opName) {
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

    private static Tuple2<AggOp, Direction> resolveAgg(String opName) {
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

    private static AggOp resolveAggOp(String opName) {
        for (Map.Entry<AggOp, String> e : Hop.HopsAgg2String.entrySet()) {
            if (e.getValue().equals(opName)) {
                return e.getKey();
            }
        }
        throw new IllegalArgumentException("[ERROR] Unrecognized AggOp: " + opName);
    }

    private static DataGenMethod resolveDataGenMethod(String opName) {
        return Hop.DataGenMethod.valueOf(opName.substring(3, opName.length() - 1).toUpperCase());
    }

    private static ReOrgOp resolveReOrgOp(String opName) {
        opName = opName.substring(2, opName.length() - 1);
        for (Map.Entry<ReOrgOp, String> e : Hop.HopsTransf2String.entrySet()) {
            if (e.getValue().equals(opName)) {
                return e.getKey();
            }
        }
        throw new IllegalArgumentException("[ERROR] Unrecognized ReOrgOp: " + opName);
    }

    private static OpOpN resolveOpOpN(String opName) {
        switch (opName.substring(2, opName.length() - 1)) {
        case "printf":
            return OpOpN.PRINTF;
        case "cbind":
            return OpOpN.CBIND;
        case "rbind":
            return OpOpN.RBIND;
        default:
            throw new IllegalArgumentException("[ERROR] Unrecognized OpOpN: " + opName);
        }
    }

    private static OpOp4 resolveOpOp4(String opName) {
        switch (opName.substring(2, opName.length() - 1)) {
        case "wsloss":
            return OpOp4.WSLOSS;
        case "wdivmm":
            return OpOp4.WDIVMM;
        case "wcemm":
            return OpOp4.WCEMM;
        case "wumm":
            return OpOp4.WUMM;
        case "wsigmoid":
            return OpOp4.WSIGMOID;
        default:
            throw new IllegalArgumentException("[ERROR] Unrecognized OpOp4: " + opName);
        }
    }

    private static OpOp3 resolveOpOp3(String opName) {
        opName = opName.substring(2, opName.length() - 1);
        for (Map.Entry<Hop.OpOp3, String> e : Hop.HopsOpOp3String.entrySet()) {
            if (e.getValue().equals(opName)) {
                return e.getKey();
            }
        }
        throw new IllegalArgumentException("[ERROR] Unrecognized OpOp3: " + opName);
    }

    private static OpOp2 resolveOpOp2(String opName) {
        opName = opName.substring(2, opName.length() - 1);
        for (Map.Entry<Hop.OpOp2, String> e : Hop.HopsOpOp2String.entrySet()) {
            if (e.getValue().equals(opName)) {
                return e.getKey();
            }
        }
        throw new IllegalArgumentException("[ERROR] Unrecognized OpOp2: " + opName);
    }

    private static OpOp1 resolveOpOp1(String opName) {
        switch (opName.substring(2, opName.length() - 1)) {
        case "cast_as_scalar":
            return Hop.OpOp1.CAST_AS_SCALAR;
        case "cast_as_matrix":
            return Hop.OpOp1.CAST_AS_MATRIX;
        case "cast_as_int":
            return Hop.OpOp1.CAST_AS_INT;
        case "cast_as_double":
            return Hop.OpOp1.CAST_AS_DOUBLE;
        case "cast_as_boolean":
            return Hop.OpOp1.CAST_AS_BOOLEAN;
        default: {
            for (Map.Entry<Hop.OpOp1, String> e : Hop.HopsOpOp12String.entrySet()) {
                if (e.getValue().equals(opName)) {
                    return e.getKey();
                }
            }
            throw new IllegalArgumentException("[ERROR] Unrecognized OpOp1: " + opName);
        }
        }
    }

    private static ValueType resolveVT(String s) {
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

    private static Expression.DataType resolveDT(String s) {
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

    /**
     * Serialize a list of hops into child-first topological order.
     * 
     * @param roots A list of HOP DAG roots
     */
    private static void serialize(List<Hop> roots, Map<Long, Hop> megaCache, String file) {
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
            megaCache.entrySet().stream()
                    .forEach(e -> System.out.println("" + e.getKey() + "\t" + e.getValue().getOpString()));
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
    private static String serializeHop(Hop hop, ArrayList<Integer> lines, Map<Long, Hop> megaCache) {
        StringBuilder sb = new StringBuilder();

        // Hop already explored, return out
        if (hop.isVisited()) {
            return sb.toString();
        }

        megaCache.put(hop.getHopID(), hop);

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

            // Matrix characteristics
            sb.append("" + hop.getDim1() + "," + hop.getDim2() + "," + hop.getRowsInBlock() + "," + hop.getColsInBlock()
                    + "," + hop.getNnz());
            if (hop.getUpdateType().isInPlace())
                sb.append("," + hop.getUpdateType().toString().toLowerCase());
            sb.append(";");

            sb.append(hop.getDataType().name().charAt(0) + ";");

            sb.append(hop.getValueType().name().charAt(0) + ";");

            // memory estimates
            sb.append(showMem(hop.getInputMemEstimate(), false) + ",")
                    .append(showMem(hop.getIntermediateMemEstimate(), false) + ",")
                    .append(showMem(hop.getOutputMemEstimate(), false) + ",")
                    .append(showMem(hop.getMemEstimate(), false) + ";");

            // data flow properties
            if (hop.requiresReblock() && hop.requiresCheckpoint())
                sb.append("rblk,chkpt");
            else if (hop.requiresReblock())
                sb.append("rblk");
            else if (hop.requiresCheckpoint())
                sb.append("chkpt");
            sb.append(";");

            // exec type
            if (hop.getExecType() != null) {
                sb.append(hop.getExecType());
            }
            sb.append(";");

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
                sb.append(";");
            }

            sb.append('\n');
        }

        hop.setVisited();
        return sb.toString();
    }

    // From Explain.java
    private static boolean isInRange(Hop hop, ArrayList<Integer> lines) {
        boolean isInRange = lines.size() == 0;
        for (int lineNum : lines) {
            if (hop.getBeginLine() == lineNum && lineNum == hop.getEndLine()) {
                return true;
            }
        }
        return isInRange;
    }

    // From Explain.java
    private static String showMem(double mem, boolean units) {
        if (mem >= OptimizerUtils.DEFAULT_SIZE) {
            return "MAX";
        }
        return OptimizerUtils.toMB(mem) + (units ? "MB" : "");
    }
}
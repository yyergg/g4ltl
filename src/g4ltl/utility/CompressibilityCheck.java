/* G4LTL: Games for LTL Synthesis
 *
 * Copyright (c) 2013, Chih-Hong Cheng, 
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *   * Redistributions of source code must retain the above copyright
 *     notice, this list of conditions and the following disclaimer.
 *   * Redistributions in binary form must reproduce the above copyright
 *     notice, this list of conditions and the following disclaimer in the
 *     documentation and/or other materials provided with the distribution.
 *   * Neither the name of the <organization> nor the
 *     names of its contributors may be used to endorse or promote products
 *     derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL Chih-Hong Cheng BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package g4ltl.utility;

import g4ltl.utility.simpleformulaparser.BooleanFormulaParser;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import jdd.bdd.BDD;

/**
 * Check compressibility of an LTL specification
 * 
 * @author Chihhong Cheng
 * @version 0.3 2013/04/08
 */
public class CompressibilityCheck {
    
    private static final int BDD_MAX_NODE_TABLE_SIZE = 20000;
    private static final int BDD_MAX_CACHE_SIZE = 4000;
    private boolean compressible;
    private ArrayList<String> newOutputVariables;
    private ArrayList<String> rewrittenOutputVariables;
    private ArrayList<String> rewrittenSpec;
    private HashMap<String, HashSet<String>> positiveVariableRewriteMap;
    private HashMap<String, HashSet<String>> negativeVariableRewriteMap;
    private ArrayList<String> outputCombinationList;
    
    public boolean isCompressible() {
        return compressible;
    }
    
    public ArrayList<String> getNewOutputVariables() {
        return newOutputVariables;
    }
    
    public ArrayList<String> getRewrittenOutputVariables() {
        return rewrittenOutputVariables;
    }
    
    public HashMap<String, HashSet<String>> getPositiveVariableRewriteMap() {
        return positiveVariableRewriteMap;
    }
    
    public HashMap<String, HashSet<String>> getNegativeVariableRewriteMap() {
        return negativeVariableRewriteMap;
    }
    
    public ArrayList<String> getOutputCombinationList() {
        return outputCombinationList;
    }
    
    public void checkCompressibility(ArrayList<String> fullSpec, ProblemDescription prob) {
        
        try {
            compressible = false;
            newOutputVariables = new ArrayList<String>();
            rewrittenOutputVariables = new ArrayList<String>();
            rewrittenSpec = new ArrayList<String>();

            // Check the following conditions; if both hold, this is an output invariant 
            // (1) a line does not use any input variables 
            // (2) a line starts with ALWAYS or [], and does not have other temporal operators

            boolean[] subspecIsOutputInvariance = new boolean[fullSpec.size()];
            for (String spec : fullSpec) {
                if (spec.trim().startsWith("[]") || spec.trim().startsWith("ALWAYS")) {
                    boolean isOutputInvariance = true;
                    // condition 1
                    for (String input : prob.getInputVariables()) {
                        if (spec.contains(input)) {
                            isOutputInvariance = false;
                            break;
                        }
                    }
                    // condition 2
                    String temporalOperators[] = {"<>", "X", "U", "EVENTUALLY", "NEXT", "UNTIL"};
                    if (isOutputInvariance) {
                        for (String op : temporalOperators) {
                            if (spec.contains(op)) {
                                isOutputInvariance = false;
                                break;
                            }
                        }
                    }

                    // condition 3 (experimental)
                    String otherLogicOperators[] = {"->", "&&"};
                    if (isOutputInvariance) {
                        for (String op : otherLogicOperators) {
                            if (spec.contains(op)) {
                                isOutputInvariance = false;
                                break;
                            }
                        }
                    }
                    
                    if (isOutputInvariance) {
                        subspecIsOutputInvariance[fullSpec.indexOf(spec)] = true;
                        // Add involved tokens
                        for (String output : prob.getOutputVariables()) {
                            if (spec.contains(output) && !rewrittenOutputVariables.contains(output)) {
                                rewrittenOutputVariables.add(output);
                            }
                        }
                    }
                }
            }
            
            BDD compression = new BDD(BDD_MAX_NODE_TABLE_SIZE, BDD_MAX_CACHE_SIZE);
            int totalNumberOfVariables = rewrittenOutputVariables.size();
            int[] vArray = new int[totalNumberOfVariables];
            for (int i = 0; i < totalNumberOfVariables; i++) {
                vArray[i] = compression.createVar();
            }
            
            int valuation = compression.getOne();
            HashSet<String> compressedVariables = new HashSet<String>();
            for (String spec : fullSpec) {
                
                if (subspecIsOutputInvariance[fullSpec.indexOf(spec)]) {
                    /*
                    System.out.println(spec);
                    String[] tokens = spec.split("[\\s\\[\\]!\\|\\(\\)]");
                    for (String token : tokens) {
                        if (!token.trim().equalsIgnoreCase("")) {
                            compressedVariables.add(token.trim());
                        }
                    }
                     * 
                     */
                    BooleanFormulaParser parser = new BooleanFormulaParser(spec.replace("[]", "ALWAYS").trim().substring("ALWAYS".length()),
                            compression, vArray, rewrittenOutputVariables, false);
                    
                    int constraint = compression.ref(parser.parse());
                    valuation = compression.andTo(valuation, constraint);
                    
                }
            }

            // Count the number of valuations and see if binary folding helps

            PrintStream out = System.out;
            ByteArrayOutputStream barray = new ByteArrayOutputStream();
            PrintStream printStreamByteArray = new PrintStream(barray);
            System.setOut(printStreamByteArray);
            compression.printSet(valuation);
            String outputCombinationFormat = barray.toString();

            // Redirect the output stream back to console again.
            System.setOut(out);
            
            if (outputCombinationFormat.trim().equalsIgnoreCase("FALSE")) {
                if (Debug.DEBUG) {
                    System.out.println("It is impossible to produce a valid output; synthesis complete");
                }
                compressible = true;
                return;
            } else if (outputCombinationFormat.trim().equalsIgnoreCase("TRUE")) {
                if (Debug.DEBUG) {
                    System.out.println("Optimization ineffective");
                }
                compressible = false;
                return;
            }
            
            HashSet<String> outputCombinationSet = new HashSet<String>();
            String[] lineArray = outputCombinationFormat.split("[\\r\\n]");
            
            for (int i = 0; i < lineArray.length; i++) {
                if (lineArray[i].length() > 1) {
                    if (!lineArray[i].contains("-")) {
                        outputCombinationSet.add(lineArray[i].trim());
                    } else {
                        outputCombinationSet.addAll(SynthesisEngine.splitVertexFromBDD(lineArray[i].trim(), 0));
                    }
                }
            }
            
            if (Math.ceil(Math.log(outputCombinationSet.size()) / Math.log(2)) == prob.getOutputVariables().size()) {
                if (Debug.DEBUG) {
                    System.out.println("Optimization is not sufficient to reduce the used bits");
                }
                compressible = false;
                return;
            } else {
                if (Debug.DEBUG) {
                    System.out.println("Optimization can reduce the used output bits from "
                            + prob.getOutputVariables().size() + " to "
                            + (int) Math.ceil(Math.log(outputCombinationSet.size()) / Math.log(2)));
                }
                compressible = true;
            }
            
            positiveVariableRewriteMap = new HashMap<String, HashSet<String>>();
            negativeVariableRewriteMap = new HashMap<String, HashSet<String>>();
            
            int numberOfNewVariables = (int) Math.ceil(Math.log(outputCombinationSet.size()) / Math.log(2));

            // When optimization is possible, generate a new specifiation based on new bit encodings, 
            outputCombinationList = new ArrayList<String>();
            outputCombinationList.addAll(outputCombinationSet);
            
            for (int i = 0; i < numberOfNewVariables; i++) {
                newOutputVariables.add("o_sig" + String.valueOf(i));
            }
            
            for (int i = 0; i < rewrittenOutputVariables.size(); i++) {
                HashSet<String> positive = new HashSet<String>();
                HashSet<String> negative = new HashSet<String>();
                HashSet<String> positiveRewrittenSet = new HashSet<String>();
                HashSet<String> negativeRewrittenSet = new HashSet<String>();
                for (int j = 0; j < outputCombinationList.size(); j++) {
                    if (outputCombinationList.get(j).charAt(i) == '1') {
                        positive.add(outputCombinationList.get(j));
                    } else {
                        negative.add(outputCombinationList.get(j));
                    }
                }
                
                if (!positive.isEmpty()) {
                    for (String s : positive) {
                        positiveRewrittenSet.add(SynthesisEngine.padZeroToString(Integer.toBinaryString(outputCombinationList.indexOf(s)), numberOfNewVariables));
                    }
                }
                positiveVariableRewriteMap.put(rewrittenOutputVariables.get(i), positiveRewrittenSet);
                
                if (!negative.isEmpty()) {
                    for (String s : negative) {
                        negativeRewrittenSet.add(SynthesisEngine.padZeroToString(Integer.toBinaryString(outputCombinationList.indexOf(s)), numberOfNewVariables));
                    }
                }
                negativeVariableRewriteMap.put("!" + rewrittenOutputVariables.get(i), negativeRewrittenSet);
                
            }

            // Perform specification rewriting (remove all lines that are output invariants)
            for (int i = 0; i < fullSpec.size(); i++) {
                if (!subspecIsOutputInvariance[i] && !fullSpec.get(i).trim().startsWith("##")) {
                    // TODO: Here there is a bug when a variable's name is a substring of other variables.
                    String str = fullSpec.get(i);

                    // First, apply on the negation case
                    for (String var : rewrittenOutputVariables) {
                        str = str.replaceAll("!" + var, reEncodeValuation("!" + var, negativeVariableRewriteMap, newOutputVariables));
                    }
                    
                    for (String var : rewrittenOutputVariables) {
                        str = str.replaceAll(var, reEncodeValuation(var, positiveVariableRewriteMap, newOutputVariables));
                    }
                    
                    rewrittenSpec.add(str);
                }
            }
            if (Debug.DEBUG) {
                System.out.println("\n---- start of rewritten spec ----\n");
                for (String s : rewrittenSpec) {
                    System.out.println(s);
                }
                System.out.println("\n---- end of rewritten spec ----\n");
            }
        } catch (Exception ex) {
            System.out.println("G4LTL: Exception appeared during the compressibility checking process!");
            compressible = false;
            newOutputVariables = new ArrayList<String>();
            rewrittenOutputVariables = new ArrayList<String>();
            rewrittenSpec = new ArrayList<String>();
            // ex.printStackTrace();
        }
    }
    
    public String getRewrittenSpecification() {
        StringBuilder result = new StringBuilder("");
        for (String s : rewrittenSpec) {
            result.append(s + "\n");
        }
        return result.toString();
    }
    
    public static String reEncodeValuation(String literal,
            HashMap<String, HashSet<String>> literalRewriteMap,
            ArrayList<String> newOutputVariables) {
        if (literalRewriteMap.get(literal).isEmpty()) {
            return "false";
        }
        
        StringBuffer returnString = new StringBuffer("(");
        
        boolean first = true;
        for (String str : literalRewriteMap.get(literal)) {
            if (first) {
                first = false;
            } else {
                returnString.append(" || ");
            }
            boolean subFirst = true;
            StringBuffer subString = new StringBuffer("(");
            for (int i = 0; i < str.length(); i++) {
                if (subFirst) {
                    subFirst = false;
                } else {
                    subString.append(" && ");
                }
                if (str.charAt(i) == '1') {
                    subString.append(newOutputVariables.get(i));
                } else {
                    subString.append("!" + newOutputVariables.get(i));
                }
            }
            subString.append(")");
            returnString.append(subString);
            
        }
        returnString.append(")");
        // System.out.println(returnString);
        return returnString.toString();
    }
}

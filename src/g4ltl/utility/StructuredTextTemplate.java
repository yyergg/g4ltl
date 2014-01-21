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

import g4ltl.utility.mealymachine.MealyMachine;
import g4ltl.utility.mealymachine.MealyMachineEdgeElement;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import jdd.bdd.BDD;

/**
 * Template for generating Structured Texts matching IEC 61131-3 standard
 * 
 * @author Chihhong Cheng
 * @version 0.3 2013/12/17
 */
public class StructuredTextTemplate {

    static String CONTROLLER_FRONT = "FUNCTION_BLOCK FB_G4LTL\n";
    static String REAR = "END_FUNCTION_BLOCK\n";

    /**
     * 
     * @param machine
     * @param prob
     * @param inputBitVectors
     * @return 
     */
    static String createSTCode(MealyMachine machine, ProblemDescription prob, ArrayList<String> inputBitVectors, boolean isCompositional) {
        StringBuilder result = new StringBuilder("");

        result.append("FUNCTION_BLOCK FB_G4LTL\n\n");
        result.append("   (* Variable definition *)\n");
        // Input variables
        result.append("   VAR_INPUT\n");
        if (prob.timerVariables.isEmpty()) {
            for (int i = 0; i < prob.getInputVariables().size(); i++) {
                result.append("      " + prob.getInputVariables().get(i) + "\t: BOOL;\n");
            }
        } else {
            for (int i = 0; i < prob.getInputVariables().size(); i++) {
                if (!prob.getInputVariables().get(i).endsWith("_expire")) {
                    result.append("      " + prob.getInputVariables().get(i) + "\t: BOOL;\n");
                }
            }
        }

        result.append("   END_VAR\n");

        // Output variables    
        result.append("   VAR_OUTPUT\n");
        if (prob.timerVariables.isEmpty()) {
            for (int i = 0; i < prob.getOutputVariables().size(); i++) {
                result.append("      " + prob.getOutputVariables().get(i) + "\t: BOOL;\n");
            }
        } else {
            for (int i = 0; i < prob.getOutputVariables().size(); i++) {
                if (!prob.getOutputVariables().get(i).endsWith("_start")) {
                    result.append("      " + prob.getOutputVariables().get(i) + "\t: BOOL;\n");
                }
            }
        }

        result.append("   END_VAR\n");

        // State and timer variables
        result.append("   VAR\n");

        result.append("   (* The total number of states equals to " + machine.getVertices().size() + " *)\n");
        result.append("      state\t: DWORD := " + (isCompositional ? String.valueOf(Integer.parseInt(machine.getInitialVertex(), 2)) : machine.getInitialVertex()) + ";\n");
        for (int i = 0; i < prob.getTimerVariables().size(); i++) {
            String name = prob.timerVariables.get(i).split("\\(")[0];
            result.append("      " + name + "\t: TON;\n");
            // String value = prob.timerVariables.get(i).split("\\(")[1].split("\\)")[0];
            // result.append("      " + name.toUpperCase() + "_VALUE\t: TIME := "+value+";\n");    
        }
        result.append("   END_VAR\n");

        // Timer constants
        if (!prob.timerVariables.isEmpty()) {
            result.append("\n   (* Constant definition *)\n");
            result.append("   VAR CONST\n");
            //result.append("      state\t: DWORD := " + (isCompositional ? String.valueOf(Integer.parseInt(machine.getInitialVertex(), 2)) : machine.getInitialVertex()) + ";\n");
            for (int i = 0; i < prob.getTimerVariables().size(); i++) {
                String name = prob.timerVariables.get(i).split("\\(")[0];
                //result.append("      " + name + "\t: TON;\n");
                String value = prob.timerVariables.get(i).split("\\(")[1].split("\\)")[0];
                result.append("      " + name.toUpperCase() + "_VALUE\t: TIME := TIME#" + value + ";\n");
            }
            result.append("   END_VAR\n");
        }


        result.append("\n   (* Control logic *)\n");
        result.append(StructuredTextTemplate.generateControllerCaseTransitions(machine, prob, inputBitVectors, isCompositional));

        result.append("\n" + StructuredTextTemplate.REAR);
        return result.toString();
    }

    static String generateControllerIfTransitions(MealyMachine machine, ProblemDescription prob, ArrayList<String> inputBitVectors, boolean isCompositional) {


        PrintStream out = System.out;

        ByteArrayOutputStream barray = new ByteArrayOutputStream();
        PrintStream printStreamByteArray = new PrintStream(barray);
        System.setOut(printStreamByteArray);

        // Maximum number of BDD nodes used in JDD.        
        int BDD_MAX_NODE_TABLE_SIZE = 1000000;
        // Maximum size of cache used in JDD.         
        int BDD_MAX_CACHE_SIZE = 200000;

        BDD bdd = new BDD(BDD_MAX_NODE_TABLE_SIZE, BDD_MAX_CACHE_SIZE);
        int totalNumberOfVariables = prob.getInputVariables().size();
        int[] variableArray = new int[totalNumberOfVariables];
        for (int i = 0; i < totalNumberOfVariables; i++) {
            variableArray[i] = bdd.createVar();
        }

        StringBuilder result = new StringBuilder("");
        HashSet<String> deterministicCtrlEdges = new HashSet<String>();
        HashSet<String> edges = new HashSet<String>();

        // Work on the bdd description for every input pattern.
        HashMap<String, Integer> inputBDDMap = new HashMap<String, Integer>();
        for (String inputVector : inputBitVectors) {
            int condition = bdd.ref(bdd.getOne());
            for (int i = 0; i < inputVector.length(); i++) {
                if (inputVector.substring(i, i + 1).equals("1")) {
                    condition = bdd.andTo(condition, variableArray[i]);
                } else {
                    condition = bdd.andTo(condition, bdd.not(variableArray[i]));
                }
            }
            inputBDDMap.put(inputVector, condition);
        }

        // The merge is possible only when the output is the same
        //  int edgeIndex = 0;
        boolean isFirstCondition = true;
        for (MealyMachineEdgeElement edge1 : machine.getEdges()) {
            // Add a mechanism to ensure determinism
            if (!deterministicCtrlEdges.contains(edge1.getSource() + "_" + edge1.getInput())) {
                deterministicCtrlEdges.add(edge1.getSource() + "_" + edge1.getInput());
                if (!edges.contains(edge1.getSource() + "_" + edge1.getDest() + "_" + edge1.getOutput())) {
                    edges.add(edge1.getSource() + "_" + edge1.getDest() + "_" + edge1.getOutput());

                    // Use bdd to compose all possible input combinations
                    int guardBdd = bdd.ref(inputBDDMap.get(edge1.getInput()));
                    for (MealyMachineEdgeElement edge2 : machine.getEdges()) {
                        if (!deterministicCtrlEdges.contains(edge2.getSource() + "_" + edge2.getInput())) {
                            if (edge1 != edge2 && edge1.getSource().equals(edge2.getSource()) && edge1.getDest().equals(edge2.getDest())
                                    && edge1.getOutput().equals(edge2.getOutput())) {
                                guardBdd = bdd.orTo(guardBdd, inputBDDMap.get(edge2.getInput()));
                            }
                        }
                    }

                    // Print the guard as string 
                    barray.reset();
                    bdd.printSet(guardBdd);
                    String foldedGuardFormat = barray.toString();
                    // System.err.println(foldedGuardFormat);
                    String[] lineArray = foldedGuardFormat.split("[\\r\\n]");

                    StringBuilder guard = new StringBuilder("");

                    boolean isFirstGuardCondition = true;
                    for (int i = 0; i < lineArray.length; i++) {
                        if (!lineArray[i].trim().equalsIgnoreCase("")) {
                            StringBuilder subGuard = new StringBuilder("(");
                            if (lineArray[i].trim().equalsIgnoreCase("true")) {
                                subGuard.append("( true )");

                            } else {
                                // represent every "-" for signal named "in" by in_isPresent
                                boolean isFirst = true;
                                for (int j = 0; j < lineArray[i].length(); j++) {
                                    if (isFirst) {
                                        if (lineArray[i].charAt(j) == '-') {
                                            subGuard.append("( TRUE )");
                                        } else {
                                            subGuard.append("(" + prob.getInputVariables().get(j) + " = " + (lineArray[i].charAt(j) == '1' ? "TRUE" : "FALSE") + ")");
                                        }
                                        isFirst = false;
                                    } else {
                                        if (lineArray[i].charAt(j) == '-') {
                                            subGuard.append(" AND  ( TRUE )");
                                        } else {
                                            subGuard.append(" AND  (" + prob.getInputVariables().get(j) + " = " + (lineArray[i].charAt(j) == '1' ? "TRUE" : "FALSE") + ")");
                                        }
                                    }
                                }
                            }
                            subGuard.append(")");
                            if (isFirstGuardCondition) {
                                guard = guard.append(subGuard);
                                isFirstGuardCondition = false;
                            } else {
                                guard = guard.append(" OR " + subGuard);
                            }
                        }
                    }
                    // System.err.println(guard.toString());

                    StringBuilder update = new StringBuilder("");
                    for (int i = 0; i < edge1.getOutput().length(); i++) {
                        if (prob.getOutputVariables().get(i).endsWith("_start")) {
                            // We only need to use trigger on positive 
                            if (edge1.getOutput().charAt(i) == '1') {
                                String name = prob.outputVariables.get(i).substring(0, prob.outputVariables.get(i).length() - "_start".length());
                                //  System.err.println(name);
                                update.append(name + "(IN:=0, PT:=" + name.toUpperCase() + "_VALUE" + "); ");
                            }
                        } else {
                            update.append(prob.getOutputVariables().get(i) + " := " + (edge1.getOutput().charAt(i) == '1' ? "TRUE" : "FALSE") + "; ");

                        }

                    }

                    if (isFirstCondition) {
                        if (isCompositional) {
                            result.append("    IF ( state = " + String.valueOf(Integer.parseInt(edge1.getSource(), 2)) + " ) AND (" + guard.toString() + ") THEN \n");
                            result.append("        state := " + String.valueOf(Integer.parseInt(edge1.getDest(), 2)) + "; " + update.toString() + " \n");
                        } else {
                            result.append("    IF ( state = " + edge1.getSource() + " ) AND (" + guard.toString() + ") THEN \n");
                            result.append("        state := " + edge1.getDest() + "; " + update.toString() + " \n");

                        }
                        isFirstCondition = false;
                    } else {
                        if (isCompositional) {

                            result.append("    ELSIF ( state = " + String.valueOf(Integer.parseInt(edge1.getSource(), 2)) + " ) AND " + guard.toString() + " THEN \n");
                            result.append("        state := " + String.valueOf(Integer.parseInt(edge1.getDest(), 2)) + "; " + update.toString() + " \n");

                        } else {

                            result.append("    ELSIF ( state = " + edge1.getSource() + " ) AND " + guard.toString() + " THEN \n");
                            result.append("        state := " + edge1.getDest() + "; " + update.toString() + " \n");

                        }
                    }
                }
            }
        }
        result.append("   END_IF;\n");
        // Redirect the output stream back to console again.
        System.setOut(out);
        return result.toString().replace("_expire", ".Q");
    }

    static String generateControllerCaseTransitions(MealyMachine machine, ProblemDescription prob, ArrayList<String> inputBitVectors, boolean isCompositional) {


        PrintStream out = System.out;

        ByteArrayOutputStream barray = new ByteArrayOutputStream();
        PrintStream printStreamByteArray = new PrintStream(barray);
        System.setOut(printStreamByteArray);

        // Maximum number of BDD nodes used in JDD.        
        int BDD_MAX_NODE_TABLE_SIZE = 1000000;
        // Maximum size of cache used in JDD.         
        int BDD_MAX_CACHE_SIZE = 200000;

        BDD bdd = new BDD(BDD_MAX_NODE_TABLE_SIZE, BDD_MAX_CACHE_SIZE);
        int totalNumberOfVariables = prob.getInputVariables().size();
        int[] variableArray = new int[totalNumberOfVariables];
        for (int i = 0; i < totalNumberOfVariables; i++) {
            variableArray[i] = bdd.createVar();
        }

        HashMap<String, StringBuilder> stateActionMap = new HashMap<String, StringBuilder>();
        // StringBuilder result = new StringBuilder("");
        HashSet<String> deterministicCtrlEdges = new HashSet<String>();
        HashSet<String> edges = new HashSet<String>();

        // Work on the bdd description for every input pattern.
        HashMap<String, Integer> inputBDDMap = new HashMap<String, Integer>();
        for (String inputVector : inputBitVectors) {
            int condition = bdd.ref(bdd.getOne());
            for (int i = 0; i < inputVector.length(); i++) {
                if (inputVector.substring(i, i + 1).equals("1")) {
                    condition = bdd.andTo(condition, variableArray[i]);
                } else {
                    condition = bdd.andTo(condition, bdd.not(variableArray[i]));
                }
            }
            inputBDDMap.put(inputVector, condition);
        }

        // The merge is possible only when the output is the same

        for (MealyMachineEdgeElement edge1 : machine.getEdges()) {
            // Add a mechanism to ensure determinism
            if (!deterministicCtrlEdges.contains(edge1.getSource() + "_" + edge1.getInput())) {
                deterministicCtrlEdges.add(edge1.getSource() + "_" + edge1.getInput());
                if (!edges.contains(edge1.getSource() + "_" + edge1.getDest() + "_" + edge1.getOutput())) {
                    edges.add(edge1.getSource() + "_" + edge1.getDest() + "_" + edge1.getOutput());

                    // Use bdd to compose all possible input combinations
                    int guardBdd = bdd.ref(inputBDDMap.get(edge1.getInput()));
                    for (MealyMachineEdgeElement edge2 : machine.getEdges()) {
                        if (!deterministicCtrlEdges.contains(edge2.getSource() + "_" + edge2.getInput())) {
                            if (edge1 != edge2 && edge1.getSource().equals(edge2.getSource()) && edge1.getDest().equals(edge2.getDest())
                                    && edge1.getOutput().equals(edge2.getOutput())) {
                                guardBdd = bdd.orTo(guardBdd, inputBDDMap.get(edge2.getInput()));
                            }
                        }
                    }

                    // Print the guard as string 
                    barray.reset();
                    bdd.printSet(guardBdd);
                    String foldedGuardFormat = barray.toString();
                    // System.err.println(foldedGuardFormat);
                    String[] lineArray = foldedGuardFormat.split("[\\r\\n]");

                    StringBuilder guard = new StringBuilder("");

                    boolean isFirstGuardCondition = true;
                    for (int i = 0; i < lineArray.length; i++) {
                        if (!lineArray[i].trim().equalsIgnoreCase("")) {
                            StringBuilder subGuard = new StringBuilder("(");
                            if (lineArray[i].trim().equalsIgnoreCase("true")) {
                                subGuard.append("( true )");

                            } else {
                                // represent every "-" for signal named "in" by in_isPresent
                                boolean isFirst = true;
                                for (int j = 0; j < lineArray[i].length(); j++) {
                                    if (isFirst) {
                                        if (lineArray[i].charAt(j) == '-') {
                                            subGuard.append("( TRUE )");
                                        } else {
                                            subGuard.append("(" + prob.getInputVariables().get(j) + " = " + (lineArray[i].charAt(j) == '1' ? "TRUE" : "FALSE") + ")");
                                        }
                                        isFirst = false;
                                    } else {
                                        if (lineArray[i].charAt(j) == '-') {
                                            subGuard.append(" AND  ( TRUE )");
                                        } else {
                                            subGuard.append(" AND  (" + prob.getInputVariables().get(j) + " = " + (lineArray[i].charAt(j) == '1' ? "TRUE" : "FALSE") + ")");
                                        }
                                    }
                                }
                            }
                            subGuard.append(")");
                            if (isFirstGuardCondition) {
                                guard = guard.append(subGuard);
                                isFirstGuardCondition = false;
                            } else {
                                guard = guard.append(" OR " + subGuard);
                            }
                        }
                    }
                    // System.err.println(guard.toString());

                    StringBuilder update = new StringBuilder("");
                    for (int i = 0; i < edge1.getOutput().length(); i++) {
                        if (prob.getOutputVariables().get(i).endsWith("_start")) {
                            // We only need to use trigger on positive 
                            if (edge1.getOutput().charAt(i) == '1') {
                                String name = prob.outputVariables.get(i).substring(0, prob.outputVariables.get(i).length() - "_start".length());
                                //  System.err.println(name);
                                update.append(name + "(IN:=0, PT:=" + name.toUpperCase() + "_VALUE" + "); ");
                            }
                        } else {
                            update.append(prob.getOutputVariables().get(i) + " := " + (edge1.getOutput().charAt(i) == '1' ? "TRUE" : "FALSE") + "; ");

                        }
                    }


                    if (isCompositional) {
                        if (stateActionMap.keySet().contains(
                                String.valueOf(Integer.parseInt(edge1.getSource(), 2)))) {

                            StringBuilder result = stateActionMap.get(String.valueOf(Integer.parseInt(edge1.getSource(), 2)));
                            result.append("    ELSIF " + guard.toString() + " THEN \n");
                            result.append("        state := " + String.valueOf(Integer.parseInt(edge1.getDest(), 2)) + "; " + update.toString() + " \n");

                        } else {
                            StringBuilder result = new StringBuilder("");
                            result.append("    IF " + guard.toString() + " THEN \n");
                            result.append("        state := " + String.valueOf(Integer.parseInt(edge1.getDest(), 2)) + "; " + update.toString() + " \n");
                            stateActionMap.put(String.valueOf(Integer.parseInt(edge1.getSource(), 2)), result);
                        }
                    } else {
                        if (stateActionMap.keySet().contains(edge1.getSource())) {
                            StringBuilder result = stateActionMap.get(edge1.getSource());
                            result.append("    ELSIF " + guard.toString() + " THEN \n");
                            result.append("        state := " + edge1.getDest() + "; " + update.toString() + " \n");
                        } else {
                            StringBuilder result = new StringBuilder("");
                            result.append("    IF " + guard.toString() + " THEN \n");
                            result.append("        state := " + edge1.getDest() + "; " + update.toString() + " \n");
                            stateActionMap.put(edge1.getSource(), result);
                        }
                    }
                }
            }
        }
        // result.append("   END_IF;\n");
        // Redirect the output stream back to console again.
        System.setOut(out);
        
        StringBuilder result = new StringBuilder("");
              result.append("CASE state OF\n");
              for(String state: stateActionMap.keySet()){
                  result.append(state+":\n");
                  result.append(stateActionMap.get(state)+"    END_IF;\n");
              }
              result.append("END_CASE;\n");
        return result.toString().replace("_expire", ".Q");
    }
}

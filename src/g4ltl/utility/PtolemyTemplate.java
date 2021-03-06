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
 * Template for generating FSMActors in MoML format.
 * 
 * @author Chihhong Cheng
 * @version 0.3 2013/02/28
 */
public class PtolemyTemplate {

    static String CONTROLLER_FRONT =
            "<?xml version=\"1.0\" standalone=\"no\"?>\n"
            + "<!DOCTYPE entity PUBLIC \"-//UC Berkeley//DTD MoML 1//EN\"\n"
            + "\t\"http://ptolemy.eecs.berkeley.edu/xml/dtd/MoML_1.dtd\">\n"
            + "<entity name=\"model\" class=\"ptolemy.domains.modal.kernel.FSMActor\">\n"
            + "\t<property name=\"_createdBy\" class=\"ptolemy.kernel.attributes.VersionAttribute\" value=\"8.0.1\">\n"
            + "\t</property>\n"
            + "<property name=\"_library\" class=\"ptolemy.moml.LibraryAttribute\">\n"
            + "\t<configure>\n"
            + "\t\t<entity name=\"StateLibrary\" class=\"ptolemy.kernel.CompositeEntity\"><input source=\"ptolemy/configs/basicUtilities.xml\"></input><entity name=\"State\" class=\"ptolemy.domains.modal.kernel.State\"><property name=\"_centerName\" class=\"ptolemy.kernel.util.Attribute\"></property></entity></entity>\n"
            + "\t</configure>\n"
            + "\t</property>\n"
            + "\t<property name=\"annotation\" class=\"ptolemy.kernel.util.Attribute\">\n"
            + "\t\t<property name=\"_hideName\" class=\"ptolemy.kernel.util.SingletonAttribute\">\n"
            + "\t</property>\n"
            + "\t<property name=\"_iconDescription\" class=\"ptolemy.kernel.util.SingletonConfigurableAttribute\">\n"
            + "\t\t<configure><svg><text x=\"20\" y=\"20\" style=\"font-size:14; font-family:SansSerif; fill:blue\">FSMActor generated by G4LTL</text></svg></configure>\n"
            + "\t</property>\n"
            + "\t\t<property name=\"_location\" class=\"ptolemy.kernel.util.Location\" value=\"[130.0, 30.0]\">\n"
            + "\t</property>\n"
            + "\t\t<property name=\"_controllerFactory\" class=\"ptolemy.vergil.basic.NodeControllerFactory\">\n"
            + "\t</property>\n"
            + "\t\t<property name=\"_editorFactory\" class=\"ptolemy.vergil.toolbox.AnnotationEditorFactory\">\n"
            + "\t</property>\n"
            + "\t</property>\n"
            + "<property name=\"_windowProperties\" class=\"ptolemy.actor.gui.WindowPropertiesAttribute\" value=\"{bounds={270, 121, 825, 525}, maximized=false}\">\n"
            + "</property>\n"
            + "<property name=\"_vergilSize\" class=\"ptolemy.actor.gui.SizeAttribute\" value=\"[600, 400]\">\n"
            + "</property>\n"
            + "<property name=\"_vergilZoomFactor\" class=\"ptolemy.data.expr.ExpertParameter\" value=\"1.0\">\n"
            + "</property>\n"
            + "<property name=\"_vergilCenter\" class=\"ptolemy.data.expr.ExpertParameter\" value=\"{300.0, 200.0}\">\n"
            + "</property>\n";
    static String MULTIPLEXER_FRONT =
            "<?xml version=\"1.0\" standalone=\"no\"?>\n"
            + "<!DOCTYPE entity PUBLIC \"-//UC Berkeley//DTD MoML 1//EN\"\n"
            + "\t\"http://ptolemy.eecs.berkeley.edu/xml/dtd/MoML_1.dtd\">\n"
            + "<entity name=\"multiplexer\" class=\"ptolemy.domains.modal.kernel.FSMActor\">\n"
            + "\t<property name=\"_createdBy\" class=\"ptolemy.kernel.attributes.VersionAttribute\" value=\"8.0.1\">\n"
            + "\t</property>\n"
            + "<property name=\"_library\" class=\"ptolemy.moml.LibraryAttribute\">\n"
            + "\t<configure>\n"
            + "\t\t<entity name=\"StateLibrary\" class=\"ptolemy.kernel.CompositeEntity\"><input source=\"ptolemy/configs/basicUtilities.xml\"></input><entity name=\"State\" class=\"ptolemy.domains.modal.kernel.State\"><property name=\"_centerName\" class=\"ptolemy.kernel.util.Attribute\"></property></entity></entity>\n"
            + "\t</configure>\n"
            + "\t</property>\n"
            + "\t<property name=\"annotation\" class=\"ptolemy.kernel.util.Attribute\">\n"
            + "\t\t<property name=\"_hideName\" class=\"ptolemy.kernel.util.SingletonAttribute\">\n"
            + "\t</property>\n"
            + "\t<property name=\"_iconDescription\" class=\"ptolemy.kernel.util.SingletonConfigurableAttribute\">\n"
            + "\t\t<configure><svg><text x=\"20\" y=\"20\" style=\"font-size:14; font-family:SansSerif; fill:blue\">Multiplexer generated by G4LTL</text></svg></configure>\n"
            + "\t</property>\n"
            + "\t\t<property name=\"_location\" class=\"ptolemy.kernel.util.Location\" value=\"[130.0, 30.0]\">\n"
            + "\t</property>\n"
            + "\t\t<property name=\"_controllerFactory\" class=\"ptolemy.vergil.basic.NodeControllerFactory\">\n"
            + "\t</property>\n"
            + "\t\t<property name=\"_editorFactory\" class=\"ptolemy.vergil.toolbox.AnnotationEditorFactory\">\n"
            + "\t</property>\n"
            + "\t</property>\n"
            + "<property name=\"_windowProperties\" class=\"ptolemy.actor.gui.WindowPropertiesAttribute\" value=\"{bounds={270, 121, 825, 525}, maximized=false}\">\n"
            + "</property>\n"
            + "<property name=\"_vergilSize\" class=\"ptolemy.actor.gui.SizeAttribute\" value=\"[600, 400]\">\n"
            + "</property>\n"
            + "<property name=\"_vergilZoomFactor\" class=\"ptolemy.data.expr.ExpertParameter\" value=\"1.0\">\n"
            + "</property>\n"
            + "<property name=\"_vergilCenter\" class=\"ptolemy.data.expr.ExpertParameter\" value=\"{300.0, 200.0}\">\n"
            + "</property>\n";
    static String REAR = "</entity>\n";

    /**
     * 
     * @param machine
     * @param prob
     * @param inputBitVectors
     * @return 
     */
    static String createPtolemyControllerCode(MealyMachine machine, ProblemDescription prob, ArrayList<String> inputBitVectors) {
        StringBuilder result = new StringBuilder("");

        result.append(PtolemyTemplate.CONTROLLER_FRONT);

        for (int i = 0; i < prob.getInputVariables().size(); i++) {
            result.append(PtolemyTemplate.generateInputPort(prob.getInputVariables().get(i), i));
        }

        for (int i = 0; i < prob.getOutputVariables().size(); i++) {
            result.append(PtolemyTemplate.generateOutputPort(prob.getOutputVariables().get(i), i));
        }

        int index = 0;
        for (String loc : machine.getVertices()) {
            if (loc.equals(machine.getInitialVertex())) {
                result.append(PtolemyTemplate.generateState(loc, true, index));
            } else {
                result.append(PtolemyTemplate.generateState(loc, false, index));
            }
            index++;
        }

        result.append(PtolemyTemplate.generateControllerConditionMergedTransitions(machine, prob, inputBitVectors));

        result.append(PtolemyTemplate.REAR);
        return result.toString();
    }

    /**
     * 
     * @param machine
     * @param prob
     * @param inputBitVectors
     * @return 
     */
    public static String createPtolemyMultiplexerCode(ArrayList<String> inputVariables,
            ArrayList<String> outputVariables, ArrayList<String> outputCombinationList) {
        StringBuilder result = new StringBuilder("");

        result.append(PtolemyTemplate.MULTIPLEXER_FRONT);

        for (int i = 0; i < inputVariables.size(); i++) {
            result.append(PtolemyTemplate.generateInputPort(inputVariables.get(i), i));
        }

        for (int i = 0; i < outputVariables.size(); i++) {
            result.append(PtolemyTemplate.generateOutputPort(outputVariables.get(i), i));
        }

        result.append(PtolemyTemplate.generateState("state", true, 0));
        result.append(PtolemyTemplate.generateMultiplexerTransitions(inputVariables, outputVariables, outputCombinationList) + "\n");
        // result.append(PtolemyTemplate.generateConditionMergedTransitions(machine, prob, inputBitVectors));

        result.append(PtolemyTemplate.REAR);
        return result.toString();
    }

    static String generateInputPort(String name, int index) {
        return "<port name=\"" + name + "\" class=\"ptolemy.actor.TypedIOPort\">\n"
                + "\t<property name=\"input\"/>\n"
                + "\t<property name=\"_location\" class=\"ptolemy.kernel.util.Location\" value=\"{20.0, " + String.valueOf(160 + 40 * index) + "}\">\n"
                + "\t</property>\n"
                + "<property name=\"_type\" class=\"ptolemy.actor.TypeAttribute\" value=\"boolean\">\n"
                + "</property>\n"
                + "<property name=\"_showName\" class=\"ptolemy.data.expr.SingletonParameter\" value=\"true\">\n"
                + "</property>\n"
                + "</port>\n";
    }

    static String generateOutputPort(String name, int index) {
        return "<port name=\"" + name + "\" class=\"ptolemy.actor.TypedIOPort\">\n"
                + "\t<property name=\"output\"/>\n"
                + "\t<property name=\"_location\" class=\"ptolemy.kernel.util.Location\" value=\"{570.0, " + String.valueOf(160 + 40 * index) + "}\">\n"
                + "\t</property>\n"
                + "<property name=\"_type\" class=\"ptolemy.actor.TypeAttribute\" value=\"boolean\">\n"
                + "</property>\n"
                + "<property name=\"_showName\" class=\"ptolemy.data.expr.SingletonParameter\" value=\"true\">\n"
                + "</property>\n"
                + "</port>\n";
    }

    static String generateState(String name, boolean isInitial, int index) {
        String horizontal = String.valueOf(120 + (index % 4) * 120);
        String vertical = String.valueOf(200 + (index / 4) * 120);
        return "<entity name=\"" + name + "\" class=\"ptolemy.domains.modal.kernel.State\">\n"
                + "<property name=\"isInitialState\" class=\"ptolemy.data.expr.Parameter\" value=\"" + (isInitial ? "true" : "false") + "\">\n"
                + "</property>\n"
                + "<property name=\"_hideName\" class=\"ptolemy.data.expr.SingletonParameter\" value=\"true\">\n"
                + "</property>\n"
                + "<property name=\"_location\" class=\"ptolemy.kernel.util.Location\" value=\"[" + horizontal + ", " + vertical + "]\">\n"
                + "</property>\n"
                + "</entity>\n";
    }

    static String generateControllerTransitions(MealyMachine machine, ProblemDescription prob) {

        StringBuilder result = new StringBuilder("");
        HashSet<String> deterministicCtrlEdges = new HashSet<String>();
        HashSet<String> edges = new HashSet<String>();

        // The merge is possible only when the output is the same
        int edgeIndex = 0;
        for (MealyMachineEdgeElement edge1 : machine.getEdges()) {
            // Add a mechanism to ensure determinism
            if (!deterministicCtrlEdges.contains(edge1.getSource() + "_" + edge1.getInput())) {
                deterministicCtrlEdges.add(edge1.getSource() + "_" + edge1.getInput());
                if (!edges.contains(edge1.getSource() + "_" + edge1.getDest() + "_" + edge1.getOutput())) {
                    edges.add(edge1.getSource() + "_" + edge1.getDest() + "_" + edge1.getOutput());

                    StringBuilder guard = new StringBuilder("(");
                    boolean isFirst = true;
                    for (int i = 0; i < edge1.getInput().length(); i++) {
                        if (edge1.getInput().charAt(i) != '-') {
                            if (isFirst) {
                                guard.append("(" + prob.getInputVariables().get(i) + " == " + (edge1.getInput().charAt(i) == '1' ? "true" : "false") + ")");
                                isFirst = false;
                            } else {
                                guard.append(" &amp;&amp; (" + prob.getInputVariables().get(i) + " == " + (edge1.getInput().charAt(i) == '1' ? "true" : "false") + ")");
                            }
                        } else {
                            if (isFirst) {
                                guard.append("(" + prob.getInputVariables().get(i).trim() + "_isPresent )");
                                isFirst = false;
                            } else {
                                guard.append(" &amp;&amp; (" + prob.getInputVariables().get(i).trim() + "_isPresent )");
                            }
                        }
                    }
                    guard.append(")");

                    for (MealyMachineEdgeElement edge2 : machine.getEdges()) {
                        if (!deterministicCtrlEdges.contains(edge2.getSource() + "_" + edge2.getInput())) {
                            if (edge1 != edge2 && edge1.getSource().equals(edge2.getSource()) && edge1.getDest().equals(edge2.getDest())
                                    && edge1.getOutput().equals(edge2.getOutput())) {

                                guard.append("&#10;|| (");
                                isFirst = true;
                                for (int i = 0; i < edge2.getInput().length(); i++) {
                                    if (edge1.getInput().charAt(i) != '-') {
                                        if (isFirst) {
                                            guard.append("(" + prob.getInputVariables().get(i) + " == " + (edge2.getInput().charAt(i) == '1' ? "true" : "false") + ")");
                                            isFirst = false;
                                        } else {
                                            guard.append(" &amp;&amp; (" + prob.getInputVariables().get(i) + " == " + (edge2.getInput().charAt(i) == '1' ? "true" : "false") + ")");
                                        }
                                    } else {
                                        if (isFirst) {
                                            guard.append("(" + prob.getInputVariables().get(i).trim() + "_isPresent )");
                                            isFirst = false;
                                        } else {
                                            guard.append(" &amp;&amp; (" + prob.getInputVariables().get(i).trim() + "_isPresent )");
                                        }
                                    }
                                }

                                guard.append(")");
                            }
                        }
                    }

                    isFirst = true;
                    StringBuilder update = new StringBuilder("");
                    for (int i = 0; i < edge1.getOutput().length(); i++) {
                        if (isFirst) {
                            update.append(prob.getOutputVariables().get(i) + " = " + (edge1.getOutput().charAt(i) == '1' ? "true" : "false"));
                            isFirst = false;
                        } else {
                            update.append(";  " + prob.getOutputVariables().get(i) + " = " + (edge1.getOutput().charAt(i) == '1' ? "true" : "false"));
                        }
                    }
                    String sourceLink = "<link port=\"" + edge1.getSource() + ".outgoingPort\" relation=\"relation" + String.valueOf(edgeIndex) + "\"/>\n";
                    String destLink = "<link port=\"" + edge1.getDest() + ".incomingPort\" relation=\"relation" + String.valueOf(edgeIndex) + "\"/>\n";


                    result.append("<relation name=\"relation" + String.valueOf(edgeIndex) + "\" class=\"ptolemy.domains.modal.kernel.Transition\">\n"
                            + "\t<property name=\"annotation\" class=\"ptolemy.data.expr.StringParameter\" value=\"\">\n"
                            + "\t</property>\n"
                            + "\t<property name=\"guardExpression\" class=\"ptolemy.kernel.util.StringAttribute\" value=\"" + guard.toString() + "\">\n"
                            + "\t</property>\n"
                            + "\t<property name=\"outputActions\" class=\"ptolemy.domains.modal.kernel.OutputActionsAttribute\" value=\"" + update.toString() + "\">\n"
                            + "\n</property>\n"
                            // + "<property name=\"nondeterministic\" class=\"ptolemy.data.expr.Parameter\" value=\"true\">\n"
                            // + "</property>\n"
                            + "</relation>\n" + sourceLink + destLink);

                }
                edgeIndex++;
            }
        }
        return result.toString();
    }

    public static String generateMultiplexerTransitions(ArrayList<String> inputVariables, ArrayList<String> outputVariables,
            ArrayList<String> outputCombinationList) {

        StringBuilder result = new StringBuilder("");


        // The merge is possible only when the output is the same
        int edgeIndex = 0;
        for (int index = 0; index < outputCombinationList.size(); index++) {

            String input = SynthesisEngine.padZeroToString(Integer.toBinaryString(index), inputVariables.size());

            StringBuilder guard = new StringBuilder("(");
            boolean isFirst = true;
            for (int i = 0; i < input.length(); i++) {
                if (input.charAt(i) != '-') {
                    if (isFirst) {
                        guard.append("(" + inputVariables.get(i) + " == " + (input.charAt(i) == '1' ? "true" : "false") + ")");
                        isFirst = false;
                    } else {
                        guard.append(" &amp;&amp; (" + inputVariables.get(i) + " == " + (input.charAt(i) == '1' ? "true" : "false") + ")");
                    }
                }

            }
            guard.append(")");

            String output = outputCombinationList.get(index);
            isFirst = true;
            StringBuilder update = new StringBuilder("");
            for (int i = 0; i < output.length(); i++) {
                if (isFirst) {
                    // If we can output arbitraty results, we prefer 0.
                    update.append(outputVariables.get(i) + " = " + (output.charAt(i) == '1' ? "true" : "false"));
                    isFirst = false;
                } else {
                    update.append(";  " + outputVariables.get(i) + " = " + (output.charAt(i) == '1' ? "true" : "false"));
                }
            }
            String sourceLink = "<link port=\"state.outgoingPort\" relation=\"relation" + String.valueOf(edgeIndex) + "\"/>\n";
            String destLink = "<link port=\"state.incomingPort\" relation=\"relation" + String.valueOf(edgeIndex) + "\"/>\n";

            result.append("<relation name=\"relation" + String.valueOf(edgeIndex) + "\" class=\"ptolemy.domains.modal.kernel.Transition\">\n"
                    + "\t<property name=\"annotation\" class=\"ptolemy.data.expr.StringParameter\" value=\"\">\n"
                    + "\t</property>\n"
                    + "\t<property name=\"guardExpression\" class=\"ptolemy.kernel.util.StringAttribute\" value=\"" + guard.toString() + "\">\n"
                    + "\t</property>\n"
                    + "\t<property name=\"outputActions\" class=\"ptolemy.domains.modal.kernel.OutputActionsAttribute\" value=\"" + update.toString() + "\">\n"
                    + "\n</property>\n"
                    + "</relation>\n" + sourceLink + destLink);

            edgeIndex++;
        }

        return result.toString();
    }

    static String generateControllerConditionMergedTransitions(MealyMachine machine, ProblemDescription prob, ArrayList<String> inputBitVectors) {


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
        int edgeIndex = 0;
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
                                // represent every signal named "in" by in_isPresent
                                boolean isFirst = true;
                                for (int j = 0; j < edge1.getInput().length(); j++) {
                                    if (isFirst) {
                                        subGuard.append("(" + prob.getInputVariables().get(j).trim() + "_isPresent )");
                                        isFirst = false;
                                    } else {
                                        subGuard.append(" &amp;&amp; (" + prob.getInputVariables().get(j).trim() + "_isPresent )");
                                    }
                                }

                            } else {
                                // represent every "-" for signal named "in" by in_isPresent
                                boolean isFirst = true;
                                for (int j = 0; j < lineArray[i].length(); j++) {
                                    if (isFirst) {
                                        if (lineArray[i].charAt(j) == '-') {
                                            subGuard.append("(" + prob.getInputVariables().get(j) + "_isPresent )");
                                        } else {
                                            subGuard.append("(" + prob.getInputVariables().get(j) + " == " + (lineArray[i].charAt(j) == '1' ? "true" : "false") + ")");
                                        }
                                        isFirst = false;
                                    } else {
                                        if (lineArray[i].charAt(j) == '-') {
                                            subGuard.append(" &amp;&amp;  (" + prob.getInputVariables().get(j) + "_isPresent )");
                                        } else {
                                            subGuard.append(" &amp;&amp;  (" + prob.getInputVariables().get(j) + " == " + (lineArray[i].charAt(j) == '1' ? "true" : "false") + ")");
                                        }
                                    }
                                }
                            }
                            subGuard.append(")");
                            if (isFirstGuardCondition) {
                                guard = guard.append(subGuard);
                                isFirstGuardCondition = false;
                            } else {
                                guard = guard.append(" &#10;|| " + subGuard);
                            }
                        }
                    }
                    // System.err.println(guard.toString());

                    boolean isFirst = true;
                    StringBuilder update = new StringBuilder("");
                    for (int i = 0; i < edge1.getOutput().length(); i++) {
                        if (isFirst) {
                            update.append(prob.getOutputVariables().get(i) + " = " + (edge1.getOutput().charAt(i) == '1' ? "true" : "false"));
                            isFirst = false;
                        } else {
                            update.append(";  " + prob.getOutputVariables().get(i) + " = " + (edge1.getOutput().charAt(i) == '1' ? "true" : "false"));
                        }
                    }
                    String sourceLink = "<link port=\"" + edge1.getSource() + ".outgoingPort\" relation=\"relation" + String.valueOf(edgeIndex) + "\"/>\n";
                    String destLink = "<link port=\"" + edge1.getDest() + ".incomingPort\" relation=\"relation" + String.valueOf(edgeIndex) + "\"/>\n";


                    result.append("<relation name=\"relation" + String.valueOf(edgeIndex) + "\" class=\"ptolemy.domains.modal.kernel.Transition\">\n"
                            + "\t<property name=\"annotation\" class=\"ptolemy.data.expr.StringParameter\" value=\"\">\n"
                            + "\t</property>\n"
                            + "\t<property name=\"guardExpression\" class=\"ptolemy.kernel.util.StringAttribute\" value=\"" + guard.toString() + "\">\n"
                            + "\t</property>\n"
                            + "\t<property name=\"outputActions\" class=\"ptolemy.domains.modal.kernel.OutputActionsAttribute\" value=\"" + update.toString() + "\">\n"
                            + "\n</property>\n"
                            // + "<property name=\"nondeterministic\" class=\"ptolemy.data.expr.Parameter\" value=\"true\">\n"
                            // + "</property>\n"
                            + "</relation>\n" + sourceLink + destLink);

                }
                edgeIndex++;
            }
        }

        // Redirect the output stream back to console again.
        System.setOut(out);
        return result.toString();
    }
}

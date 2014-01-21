/* G4LTL: Games for LTL Synthesis
 *
 * Copyright (c) 2013, Chih-Hong Cheng 
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

/**
 * Template for generating controllers in SAL format. SAL is a model checker
 * developed by SRI International.
 * 
 * @author Chihhong Cheng
 * @version 0.3 2013/02/28
 */
public class SALTemplate {

    static String createSALCode(MealyMachine machine, ProblemDescription prob, String solverName) {

        StringBuilder result = new StringBuilder("");

        result.append("%% Automatically generated by G4LTL (" + solverName + ") \n");
        result.append("%% Please save it with the name G4LTL.sal \n");
        result.append("%% NOTICE: LTL specification may require adding parentheses. \n");
        result.append("%% NOTICE: \"a U b\" needs to be manually rewritten as U (a, b) \n\n");

        result.append("G4LTL: CONTEXT = \n");
        result.append("BEGIN\n");
        result.append("State: TYPE = {");

        boolean first = true;
        for (String loc : machine.getVertices()) {
            if (first) {
                result.append("s" + loc);
                first = false;
            } else {
                result.append(", s" + loc);
            }
        }
        result.append(" };\n");



        result.append("\tmain: MODULE =\n");
        result.append("\tBEGIN \n");
        result.append("\t\tINPUT  ");
        first = true;
        for (String inSig : prob.getInputVariables()) {
            if (first) {
                result.append(inSig);
                first = false;
            } else {
                result.append(", " + inSig);
            }
        }
        result.append(" : BOOLEAN\n");

        result.append("\t\tOUTPUT ");
        first = true;
        for (String outSig : prob.getOutputVariables()) {
            if (first) {
                result.append(outSig);
                first = false;
            } else {
                result.append(", " + outSig);
            }
        }
        result.append(" : BOOLEAN\n");
        result.append("\t\tOUTPUT state : State\n");
        result.append("\t\tINITIALIZATION\n");

        result.append("\t\t\tstate = s" + machine.getInitialVertex());
        result.append("\n");

        result.append("\t\tTRANSITION\n");
        result.append("\t\t[\n");

        int transitionIndex = 0;
        first = true;
        for (MealyMachineEdgeElement edge : machine.getEdges()) {

            String stateInfo = "(state = s" + edge.getSource() + ")";


            if (first) {
                first = false;
            } else {
                result.append("\n\t\t\t[]");
            }
            result.append("\n\t\tt" + String.valueOf(transitionIndex++) + ":");
            result.append("\n\t\t\t" + stateInfo + "  ");
            String input = edge.getInput();
            for (int i = 0; i < input.length(); i++) {
                if (input.charAt(i) != '-') {
                    result.append(" and (" + prob.getInputVariables().get(i) + " = " + (input.charAt(i) == '1' ? "true" : "false") + ")");
                }
            }
            result.append("\n\t\t\t--> state' = s" + edge.getDest());

            String output = edge.getOutput();
            for (int i = 0; i < output.length(); i++) {
                // If the output is "-", then we just output it to be "false"
                result.append(";  " + prob.getOutputVariables().get(i) + "' = " + (output.charAt(i) == '1' ? "true" : "false"));
            }

        }

        result.append("\n\t\t]\n");

        result.append("\tEND;\n");

        // Annotate the LTL specification fitting the SAL format
        String ltlSpec = prob.getLtlSpecification();
        ltlSpec = ltlSpec.replaceAll("\\[\\]", " G ");
        ltlSpec = ltlSpec.replaceAll("<>", " F ");
        ltlSpec = ltlSpec.replaceAll("->", "=>");
        ltlSpec = ltlSpec.replaceAll("&&", " AND ");
        ltlSpec = ltlSpec.replaceAll("\\|\\|", " OR ");
        ltlSpec = ltlSpec.replaceAll("!", " not ");
        for (String output : prob.getOutputVariables()) {
            ltlSpec = ltlSpec.replaceAll(output, "( X (" + output + ") )");
        }

        result.append("\n\ttheo: THEOREM main |- " + ltlSpec + ";");
        result.append("\nEND");


        return result.toString();
    }
}
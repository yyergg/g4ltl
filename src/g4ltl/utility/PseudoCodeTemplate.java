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
 * Template for generating pseudo code.
 * 
 * @author Chihhong Cheng
 * @version 0.3 2013/02/28
 */
public class PseudoCodeTemplate {

    static String createPsuedoCode(MealyMachine machine, ProblemDescription prob, String solverName) {
        StringBuilder result = new StringBuilder("");

        result.append("%% Automatically generated by G4LTL (" + solverName + ") \n");
        result.append("INPUT:  " + prob.getInputVariables().toString() + "\n");
        result.append("OUTPUT: " + prob.getOutputVariables().toString() + "\n");
        result.append("VAR state := " + machine.getInitialVertex() + "\n");

        result.append("\nControl-function() {\n");
        result.append("  WHILE (1) {\n");
        result.append("    Read-input(); \n");

        boolean firstCondition = true;
        for (MealyMachineEdgeElement e : machine.getEdges()) {
            if (firstCondition) {
                result.append("    IF state == " + e.getSource() + " AND input == <" + e.getInput() + "> THEN {\n");
                result.append("        state := " + e.getDest() + ";  output <" + e.getOutput() + ">;\n\n");
                firstCondition = false;
            } else {
                result.append("    } ELSE IF state == " + e.getSource() + " AND input == <" + e.getInput() + "> THEN {\n");
                result.append("        state := " + e.getDest() + ";  output <" + e.getOutput() + ">;\n\n");
            }
        }

        result.append("    }\n");
        result.append("  }\n");
        result.append("}\n");

        return result.toString();

    }
}

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

import java.util.ArrayList;

/**
 * Store the problem (or subproblem) in a unified structure to be passed to 
 * the synthesis engine.
 * 
 * @author Chihhong Cheng
 * @version 0.2 2012/08/08
 */
public class ProblemDescription {

    protected ArrayList<String> inputVariables;
    protected ArrayList<String> outputVariables;
    protected ArrayList<String> timerVariables;    
    protected String ltlSpecification;
    protected int unrollSteps;

    public ProblemDescription() {
        inputVariables = new ArrayList<String>();
        outputVariables = new ArrayList<String>();
        timerVariables = new ArrayList<String>();
    }
    
    public boolean hasNextOperator(){
       if(ltlSpecification.contains("X") || ltlSpecification.contains("NEXT")){
           return true;
       } else {
           return false;
       }
    }
    
    public ProblemDescription(ArrayList<String> inputSignals, ArrayList<String> outputSignals,
            ArrayList<String> timerSignals,
            String ltlSpecification, int unrollSteps) {

        this.inputVariables = inputSignals;
        this.outputVariables = outputSignals;
        this.timerVariables = timerSignals;
        this.ltlSpecification = ltlSpecification;
        this.unrollSteps = unrollSteps;

    }

    public void setInputVariables(ArrayList<String> input) {
        this.inputVariables = input;
    }

    public ArrayList<String> getInputVariables() {
        return this.inputVariables;
    }

    public void setOutputVariables(ArrayList<String> output) {
        this.outputVariables = output;
    }

    public ArrayList<String> getOutputVariables() {
        return this.outputVariables;
    }

        public void setTimerVariables(ArrayList<String> timer) {
        this.timerVariables = timer;
    }

    public ArrayList<String> getTimerVariables() {
        return this.timerVariables;
    }
    
    public void setLtlSpecification(String spec) {
        this.ltlSpecification = spec;
    }

    public String getLtlSpecification() {
        return this.ltlSpecification;
    }

    public void setUnrollSteps(int step) {
        this.unrollSteps = step;
    }

    public int getUnrollSteps() {
        return this.unrollSteps;
    }

}

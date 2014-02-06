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
package g4ltl.gametranslation.cobuechi;

import java.util.Arrays;
import java.util.HashMap;
import java.util.TreeSet;

/**
 * EquivalenceClass.java Purpose: The unit to store basic equivalence class for
 * a node in the safety game (which is translated from a Co-Buechi game). Here
 * the accumulator is achieved by using an array of 32 bit integers, rather than
 * explicit set inclusion.
 *
 * @author Chihhong Cheng
 * @version 0.2 2012/08/08
 */
public class EquivalenceClass {
    
    public boolean isFail;
    
    public int id;
    /**
     * Whether the node belongs to environment.
     */
    public boolean isEnv;
    /**
     * The current visited number, for each unsafe states. score[number of
     * vertices in Co-buechi][number of final (bad) vertices in Co-buechi].
     * score[i][j] means that for the current env state [i] (if isEnv == false
     * then for the one-step predecessor env state), the number of visited times
     * for final vertex indexed j.
     */
    public int[][] score;
    /**
     * The currently visited env vertex.
     */
    // public int[] accumulator;
    public TreeSet<Integer> accumulator;
    /**
     * The currently visited ctrl vertex.
     */
    public TreeSet<Integer> controlVertex;
    /**
     * Successor of the current node.
     */
    public HashMap<String, EquivalenceClass> successor;
    /**
     * If isEnv == true, what is the curresponding input vector.
     */
    String inputVector = "";

    public EquivalenceClass(boolean isEnv) {
        this.isEnv = isEnv;
        score = new int[CoBuechiSafetyReduction.sizeOfEnvVertices][CoBuechiSafetyReduction.sizeOfScoreArray];
        accumulator = new TreeSet<Integer>(); //new int[CoBuechiSafetyReduction.sizeOfAccumulatorArray];
        controlVertex = new TreeSet<Integer>(); //new int[CoBuechiSafetyReduction.sizeOfAccumulatorArray];
        successor = new HashMap<String, EquivalenceClass>();
    }

    
    public EquivalenceClass(boolean isEnv, int[][] score) {
        this.isEnv = isEnv;
        this.score = new int[CoBuechiSafetyReduction.sizeOfEnvVertices][CoBuechiSafetyReduction.sizeOfScoreArray];
        for (int i = 0; i < CoBuechiSafetyReduction.sizeOfEnvVertices; i++) {
            System.arraycopy(score, 0, this.score, 0, CoBuechiSafetyReduction.sizeOfScoreArray);
        }
        accumulator = new TreeSet<Integer>(); //new int[CoBuechiSafetyReduction.sizeOfAccumulatorArray];
        controlVertex = new TreeSet<Integer>(); //new int[CoBuechiSafetyReduction.sizeOfAccumulatorArray];
        successor = new HashMap<String, EquivalenceClass>();
    } 

    @Override
    public boolean equals(Object obj) {
        // Whenever a.equals(b), then a.hashCode() must be same as b.hashCode().
        if (isEnv == ((EquivalenceClass) obj).isEnv
                && inputVector.equals(((EquivalenceClass) obj).inputVector)
                && accumulator.equals(((EquivalenceClass) obj).accumulator)
                // && Arrays.equals(accumulator, ((EquivalenceClass) obj).accumulator)
                && controlVertex.equals(((EquivalenceClass) obj).controlVertex) // && Arrays.equals(controlVertex, ((EquivalenceClass) obj).controlVertex)
                ) {
            for (int i = 0; i < score.length; i++) {
                if (!Arrays.equals(score[i], ((EquivalenceClass) obj).score[i])) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    @Override
    public int hashCode() {

        int hash = 0;
        for (Integer s : this.accumulator) {
            hash += s.intValue();
        }
        for (Integer s : this.controlVertex) {
            hash += s.intValue();
        }
        // for (int i = 0; i < controlVertex.length; i++) {
        //     hash += controlVertex[i];
        // }
        if (isEnv) {
            return hash;
        } else {
            return -1 * hash;
        }

    }
}

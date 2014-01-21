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

import g4ltl.arena.EdgeElement;
import g4ltl.arena.GameArena;
import g4ltl.arena.VertexEdgeSet;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

/**
 * CoBuechiSafetyReduction.java Purpose: Perform the translation from a CoBuechi
 * game to a safety game. By doing so we ensure that player 0 (control) may
 * still find the strategy, if the unrolling is sufficiently large.
 *
 * @author Chihhong Cheng
 * @version 0.2 2012/08/08
 */
public class CoBuechiSafetyReduction {

    /**
     * Store the set of vertices in the equivalence graph (env only, for checking).
     */
    private HashMap<EquivalenceClass, EquivalenceClass> equiGraphEnv;
    /**
     * Store the set of vertices in the equivalence graph (for game creation)
     */
    private ArrayList<EquivalenceClass> equiGraph;
    /**
     * Initial vertex of the generated safety game.
     */
    public EquivalenceClass initialVertex;
    /**
     * Unique risk vertex of the generated safety game.
     */
    public EquivalenceClass riskVertex;
    /**
     * Original Co-Buechi arena.
     */
    GameArena game;
    /**
     * Corresponding id-VertexEdgeSet map of the original Co-Buechi game for
     * fast accessing the vertex.
     */
    HashMap<Integer, VertexEdgeSet> gameVertexMap;
    /**
     * The set of final states in the original Co-Buechi game (which is
     * considered to be risk).
     */
    ArrayList<Integer> riskStates;
    /**
     * An array of environment states in the Co-Buechi game.
     */
    ArrayList<Integer> environmentStates;
    // Given an environment vertex in the original game, return its index in the environmentStates
    int[] environmentStatesIndex;
    /**
     * The worklist is used to store the remaining vertices to be processed. The
     * depthList is used to store the corresponding depth of the vertex (for
     * on-the-fly expansion).
     */
    ArrayList<EquivalenceClass> worklist;
    ArrayList<Integer> depthList;
    /**
     * The dimension of the score function.
     */
    static public int sizeOfScoreArray;
    /**
     * The dimension of the accumulator.
     */
    static public int sizeOfAccumulatorArray;
    /**
     * The number of environment variables.
     */
    static public int sizeOfEnvVertices;
    /**
     * The size of input domain.
     */
    static public int sizeOfInputDomain;
    HashMap<Integer, HashSet<Integer>> vertexOutputDestinationMap;
    // Applying this factor means that the maximum allowed output variable bits is limited to 6
    static int FACTOR = 128;
    // Caching to avoid redundant computation
    HashMap<String, HashSet<Integer>> successorVertexMap;
    // globalIndex for the translated safety game
    int vertexIndex = 0;

    /**
     * Constructor.
     *
     * @param game the arena of the Co-Buechi game.
     * @param riskStates the set of final states (i.e., risk states) in the
     * Co-Buechi game.
     * @param sizeOfInput the number of possible input combinations in LTL
     * synthesis.
     */
    public CoBuechiSafetyReduction(GameArena game, ArrayList<Integer> riskStates, int sizeOfInput, ArrayList<String> inputVector, ArrayList<String> outputVector) {
        vertexIndex = 0;
        this.equiGraphEnv = new HashMap<EquivalenceClass, EquivalenceClass>();
        this.equiGraph = new ArrayList<EquivalenceClass>();
        this.game = game;
        this.riskStates = riskStates;
        sizeOfScoreArray = riskStates.size();
        sizeOfAccumulatorArray = (int) Math.ceil(game.vertexList.size() / 32.0);
        this.gameVertexMap = new HashMap<Integer, VertexEdgeSet>();
        this.environmentStates = new ArrayList<Integer>();
        for (VertexEdgeSet v : game.vertexList) {
            if (v.getVertexProperty() == VertexEdgeSet.INITIAL_PLANT
                    || v.getVertexProperty() == VertexEdgeSet.NONINITIAL_PLANT) {
                this.environmentStates.add(Integer.valueOf(v.getVertexID()));
            }
            this.gameVertexMap.put(Integer.valueOf(v.getVertexID()), v);
        }

        environmentStatesIndex = new int[game.vertexList.size()];
        for (int i = 0; i < environmentStates.size(); i++) {
            environmentStatesIndex[environmentStates.get(i).intValue()] = i;
        }
        sizeOfEnvVertices = this.environmentStates.size();
        sizeOfInputDomain = sizeOfInput;

        vertexOutputDestinationMap = new HashMap<Integer, HashSet<Integer>>();
        for (VertexEdgeSet v : this.game.vertexList) {
            if (v.getVertexProperty() == VertexEdgeSet.NONINITIAL_CONTROL
                    || v.getVertexProperty() == VertexEdgeSet.INITIAL_CONTROL) {
                for (String output : outputVector) {
                    HashSet<Integer> set = new HashSet<Integer>();
                    for (EdgeElement e : v.edgeSet) {
                        if (e.getEdgeLabel().contains(output)) {
                            set.add(Integer.valueOf(e.getDestVertexID()));
                        }
                    }
                    vertexOutputDestinationMap.put(Integer.valueOf(v.getVertexID() * FACTOR + Integer.valueOf(output, 2)), set);
                }
            }
        }


        // Caching the successor vertices for all environment vertices
        successorVertexMap = new HashMap<String, HashSet<Integer>>();
        for (Integer i : gameVertexMap.keySet()) {
            if (gameVertexMap.get(i).getVertexProperty() == VertexEdgeSet.NONINITIAL_PLANT
                    || gameVertexMap.get(i).getVertexProperty() == VertexEdgeSet.INITIAL_PLANT) {

                for (String input : inputVector) {
                    HashSet<Integer> set = new HashSet<Integer>();
                    VertexEdgeSet v = gameVertexMap.get(i);
                    for (EdgeElement e : v.edgeSet) {
                        if (e.getEdgeLabel().contains(input)) {
                            set.add(e.getDestVertexID());
                            break;
                        }
                    }
                    successorVertexMap.put(String.valueOf(i) + input, set);
                }
            }
        }
    }

    /**
     * Generate the safety game arena via an un-the-fly expansion.
     *
     * @return The safety game arena
     */
    public ArrayList<EquivalenceClass> createReductionGraph(String initialVertexID, int unrollingOption,
            int unrollDepth, int riskBound, ArrayList<String> inputVectors, ArrayList<String> outputVectors) {

        // Create the worklist
        worklist = new ArrayList<EquivalenceClass>();
        depthList = new ArrayList<Integer>();

        // Create the equivalence class of the initial vertex
        initialVertex = new EquivalenceClass(true);
        setAccumulator(initialVertex, Integer.parseInt(initialVertexID));

        for (int i = 0; i < riskStates.size(); i++) {
            if (riskStates.contains(Integer.valueOf(initialVertexID))) {
                int sourceEnvVertex = (Integer.parseInt(initialVertexID) / (sizeOfInputDomain + 1));
                initialVertex.score[sourceEnvVertex][riskStates.indexOf(Integer.valueOf(initialVertexID))] = 1;
            }
        }
        initialVertex.id = vertexIndex++;

        equiGraphEnv.put(initialVertex, initialVertex);
        equiGraph.add(initialVertex);

        // Create the risk vertex (as env vertex)
        riskVertex = new EquivalenceClass(true);
        for (int i = 0; i < riskStates.size(); i++) {
            riskVertex.score[i][i] = riskBound;
        }
        riskVertex.id = vertexIndex++;
        equiGraphEnv.put(riskVertex, riskVertex);
        equiGraph.add(riskVertex);

        // Unroll the graph partially
        worklist.add(initialVertex);
        depthList.add(Integer.valueOf(0));
        unrollOnTheFly(unrollDepth, riskBound, inputVectors, outputVectors);

        return equiGraph;

        //  ArrayList<EquivalenceClass> list = new ArrayList<EquivalenceClass>();

        // Assign each vertex in the generated reduction graph with an unique id.

        /*
        int index = 0;
        for (EquivalenceClass v : equiGraphEnv.values()) {
        v.id = index++;
        list.add(v);
        }
        for (EquivalenceClass v : equiGraphCtrl.values()) {
        v.id = index++;
        list.add(v);
        }
         */

        // return list;
    }

    private void setAccumulator(EquivalenceClass element, int vertex) {
        element.accumulator.add(Integer.valueOf(vertex));
        // int quotient = vertex / 32;
        // int remainder = vertex % 32;
        // element.accumulator[quotient] = element.accumulator[quotient] | (1 << remainder);
    }

    private void setControlVertex(EquivalenceClass element, int vertex) {
        element.controlVertex.add(Integer.valueOf(vertex));
        // int quotient = vertex / 32;
        // int remainder = vertex % 32;
        // element.controlVertex[quotient] = element.controlVertex[quotient] | (1 << remainder);
    }

    private void setControlVertices(EquivalenceClass element, HashSet<Integer> vertices) {
        element.controlVertex.addAll(vertices);

    }

    /**
     * Expand the arena by an unrolling of a user-specified depth.
     *
     * @param maxiDepth user-specifed depth
     * @param riskBound
     * @param inputVectors all possible input vector in LTL synthesis
     * @param outputVectors all possible output vector in LTL synthesis
     */
    private void unrollOnTheFly(int maxiDepth, int riskBound, ArrayList<String> inputVectors, ArrayList<String> outputVectors) {
        do {
            if (worklist.isEmpty() == true) {
                break;
            }

            // Take out the element from the list, together with the current depth.
            EquivalenceClass currentEqivClass = worklist.remove(0);
            int depth = depthList.remove(0).intValue();

            if (currentEqivClass.isEnv == false) {                                                
                // Control vertex
                for (String output : outputVectors) {
                    // Create its successor vertex (environment vertex)
                    EquivalenceClass succVertex = new EquivalenceClass(true);
                    
                   // EquivalenceClass succVertex = new EquivalenceClass(true, currentEqivClass.score);

                    // See if currentEquiClass contains frontier vertex i. If so, compute all of its successors by 
                    // using the output vector. 
                    //
                    // Originally, we should track for every frontier (during the expansion process), 
                    // what is the score. In this way, we may have a single frontier having two different
                    // score, because two different paths reach the same frontier vertex. This means that 
                    // for each frontier vertex, we may need to keep an antichain e.g., {(2,1,2) (1,3,2)} 
                    // to represent possible scores when visiting this vertex.
                    // 
                    // Here we perform a simplication. If two vertices in the current set visits the same 
                    // destination vertex v, we let the value of v have the max score of two current vertices,
                    // plus the effect whether such a destination vertex is a bad final state 
                    // (if so then we need to add 1,  but only once)

                   // boolean isFirst = true;

                    for (Integer i : currentEqivClass.controlVertex) {
                        VertexEdgeSet v = gameVertexMap.get(i);
                        int sourceEnvVertex = (v.getVertexID() / (sizeOfInputDomain + 1)) * (sizeOfInputDomain + 1);

                        for (Integer dest : vertexOutputDestinationMap.get(Integer.valueOf(v.getVertexID() * FACTOR + Integer.valueOf(output, 2)))) {
                     
                            /*
                            if (isFirst) {
                                for (int j = 0; j < riskStates.size(); j++) {
                                    System.arraycopy(currentEqivClass.score[environmentStatesIndex[sourceEnvVertex]], 0,
                                            succVertex.score[environmentStatesIndex[dest.intValue()]], 0, currentEqivClass.score[environmentStatesIndex[sourceEnvVertex]].length);
                                }
                                isFirst = false;
                            } 
                             * 
                             */
                             

                            // Set the vertex to be visited 
                            setAccumulator(succVertex, dest.intValue());
                            // Compare the current score value with the possible value derived from the source. 

                            if (riskStates.contains(dest)) {
                                for (int j = 0; j < riskStates.size(); j++) {
                                    if (j == riskStates.indexOf(dest)) {
                                        /*
                                        succVertex.score[environmentStatesIndex[dest.intValue()]][j] = Math.max(succVertex.score[environmentStatesIndex[dest.intValue()]][j], 
                                        currentEqivClass.score[environmentStatesIndex[sourceEnvVertex]][j]+1);                                        
                                        */
                                        if (succVertex.score[environmentStatesIndex[dest.intValue()]][j]
                                                < currentEqivClass.score[environmentStatesIndex[sourceEnvVertex]][j] + 1) {
                                            succVertex.score[environmentStatesIndex[dest.intValue()]][j] = currentEqivClass.score[environmentStatesIndex[sourceEnvVertex]][j] + 1;
                                        }

                                    } else {
                                        /*
                                        succVertex.score[environmentStatesIndex[dest.intValue()]][j] = Math.max(succVertex.score[environmentStatesIndex[dest.intValue()]][j], 
                                        currentEqivClass.score[environmentStatesIndex[sourceEnvVertex]][j]);                                        
                                         * 
                                         */
                                        if (succVertex.score[environmentStatesIndex[dest.intValue()]][j]
                                                < currentEqivClass.score[environmentStatesIndex[sourceEnvVertex]][j]) {
                                            succVertex.score[environmentStatesIndex[dest.intValue()]][j] = currentEqivClass.score[environmentStatesIndex[sourceEnvVertex]][j];
                                        }
                                    }
                                }
                            } else {
                                for (int j = 0; j < riskStates.size(); j++) {
                                    /*
                                    succVertex.score[environmentStatesIndex[dest.intValue()]][j] = Math.max(succVertex.score[environmentStatesIndex[dest.intValue()]][j], 
                                    currentEqivClass.score[environmentStatesIndex[sourceEnvVertex]][j]);                                    
                                     */
                                    if (succVertex.score[environmentStatesIndex[dest.intValue()]][j]
                                            < currentEqivClass.score[environmentStatesIndex[sourceEnvVertex]][j]) {
                                        succVertex.score[environmentStatesIndex[dest.intValue()]][j] = currentEqivClass.score[environmentStatesIndex[sourceEnvVertex]][j];
                                    }
                                }
                            }
                        }
                    }

                    // variable used for detecting such a vertex can be replaced by risk.
                    boolean replaceByRisk = false;

                    outer:
                    for (int i = 0; i < this.environmentStates.size(); i++) {
                        for (Integer risk : riskStates) {
                            if (succVertex.score[i][riskStates.indexOf(risk)] >= riskBound) {
                                replaceByRisk = true;
                                break outer;
                            }
                        }
                    }

                    if (replaceByRisk) {
                        currentEqivClass.successor.put(output, riskVertex);
                    } else {
                        if (equiGraphEnv.get(succVertex) != null) {
                            currentEqivClass.successor.put(output, equiGraphEnv.get(succVertex));
                        } else {
                            if (depth + 1 > maxiDepth) {
                                // This vertex can not be fully expanded, replace it by risk
                                currentEqivClass.successor.put(output, riskVertex);
                            } else {
                                succVertex.id = vertexIndex++;
                                equiGraphEnv.put(succVertex, succVertex);
                                equiGraph.add(succVertex);
                                currentEqivClass.successor.put(output, succVertex);
                                worklist.add(succVertex);
                                depthList.add(Integer.valueOf(depth + 1));
                            }
                        }
                    }
                }

            } else {

                // Environment vertex                             
                for (String input : inputVectors) {

                    if (depth + 1 > maxiDepth) {
                        currentEqivClass.successor.put(input, riskVertex);
                        // As currentEqivClass is an environment vertex, we just stop adding further edges.
                        break;

                    } else {

                        EquivalenceClass succVertex = new EquivalenceClass(false);
                        succVertex.score = currentEqivClass.score;
                        succVertex.inputVector = input;

                        for (Integer i : currentEqivClass.accumulator) {

                            // With caching
                            setControlVertices(succVertex, successorVertexMap.get(String.valueOf(i) + input));

                            // Without caching
                            // It contains vertex i, then compute all of its successors via input vector.
                        /*
                            VertexEdgeSet v = gameVertexMap.get(i);
                            for (EdgeElement e : v.edgeSet) {
                            if (e.getEdgeLabel().contains(input)) {
                            setControlVertex(succVertex, e.getDestVertexID());
                            // For the control vertex, the score is just the duplication of the score in the source.
                            }
                            }
                             * 
                             */

                        }


                        // If the vertex appears previously, then link to that vertex.
                        // Notice: it shall not appear for control vertex.
                        // if (equiGraphCtrl.get(succVertex) != null) {
                        //    currentEqivClass.successor.put(input, equiGraphCtrl.get(succVertex));                      
                        // } else {

                        // equiGraphCtrl.put(succVertex, succVertex);
                        succVertex.id = vertexIndex++;
                        equiGraph.add(succVertex);
                        currentEqivClass.successor.put(input, succVertex);
                        worklist.add(succVertex);
                        depthList.add(Integer.valueOf(depth + 1));
                    }
                    // }
                }
            }
        } while (true);


    }
}

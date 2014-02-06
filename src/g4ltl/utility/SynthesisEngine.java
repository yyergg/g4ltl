
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

import g4ltl.arena.EdgeElement;
import g4ltl.arena.GameArena;
import g4ltl.arena.VertexEdgeSet;
import g4ltl.gametranslation.cobuechi.CoBuechiSafetyReduction;
import g4ltl.gametranslation.cobuechi.EquivalenceClass;
import g4ltl.utility.mealymachine.MealyMachine;
import g4ltl.utility.mealymachine.MealyMachineEdgeElement;
import gov.nasa.ltl.graph.Edge;
import gov.nasa.ltl.graph.Graph;
import gov.nasa.ltl.graph.Node;
import gov.nasa.ltl.trans.LTL2Buchi;
import gov.nasa.ltl.trans.ParseErrorException;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.StringTokenizer;
import java.util.logging.Level;
import java.util.logging.Logger;
import jdd.bdd.BDD;
import jdd.bdd.Permutation;

/**
 * The backend synthesis engine, including a symbolic safety game solver.
 *
 * @author Chihhong Cheng
 * @version 1.0 2013/10/04
 */
public class SynthesisEngine {

    public ArrayList<EquivalenceClass> lastSafetyGameArena;
    
    /**
     *  Solver option: Co-Buechi + safety.
     */
    public static int COBUECHI_SOLVER = 0;
    /** 
     * Solver option: Buechi.
     */
    public static int BUECHI_SOLVER = 1;
    /** 
     * Output option: pseudo code format.
     */
    public static int OUTPUT_PSUEDO_CODE = 0;
    /** 
     * Output option: SAL format (SAL is a model checker by SRI International).
     */
    public static int OUTPUT_SAL = 1;
    /** 
     * Output option: Ptolemy II FSMACtor format (Ptolemy II is developed by UC Berkeley).
     */
    public static int OUTPUT_FSM_ACTOR_PTOLEMY = 2;
    /** 
     * Output option: Ptolemy II FSMACtor format (Ptolemy II is developed by UC Berkeley).
     */
    public static int OUTPUT_STRUCTURED_TEXT = 3;
    /**
     * Maximum number of BDD nodes used in JDD.
     */
    private static final int BDD_MAX_NODE_TABLE_SIZE = 4000000;
    /**
     * Maximum size of cache used in JDD.
     */
    private static final int BDD_MAX_CACHE_SIZE = 800000;
    /**
     * BDD data structure used in the synthesis engine.
     */
    private BDD bdd = new BDD(BDD_MAX_NODE_TABLE_SIZE, BDD_MAX_CACHE_SIZE);
    /**
     * Array that maintains the ordering of variables used in BDD.
     */
    private int[] variableArray;
    /**
     * Data structure to store the index-name pair of each arena.
     */
    private ArrayList<String> vertexNameBuechiAutomaton;
    private ArrayList<String> vertexNameArena;
    /**
     * Maximumly allowed visited final states in Co-Buechi automata.
     */
    private static int MAX_VISIT_COBUECHI_FINAL_STATE = 5;

    /**
     * Solve a Buechi game symbolically and generate a controller (Mealy Machine).
     * 
     * @param gameArena Buechi game in graph form
     * @param finalEnvVertices indices for final vertices
     * @param proveExistence prove existence of strategy or prove non-existence by finding a counter-strategy
     * @return MealyMachine as a strategy (having explicit variable to answer a strategy is found)
     */
    private MealyMachine analyzeBuechiGame(GameArena gameArena,
            ArrayList<Integer> finalEnvVertices, boolean proveExistence) {

        // Step 1-a: Clean up the memory previously used in BDD, and assign new memory for them.
        bdd.cleanup();

        bdd = new BDD(BDD_MAX_NODE_TABLE_SIZE, BDD_MAX_CACHE_SIZE);

        // Step 1-b: Declare the variable for controller strategies.
        int strategy = bdd.getZero();

        // Step 2-a: Decide and declare the number of variables used in the BDD. 

        int totalNumberOfVariables = ((int) (Math.ceil(Math.log10(gameArena.vertexList.size()) / Math.log10(2)))) * 2;
        int NUM_OF_BITS_FOR_STATE = (int) (Math.ceil(Math.log10(gameArena.vertexList.size()) / Math.log10(2)));

        if (NUM_OF_BITS_FOR_STATE == 0) {
            NUM_OF_BITS_FOR_STATE = 1;
            totalNumberOfVariables += 2;
        }

        variableArray = new int[totalNumberOfVariables];
        for (int i = 0; i < totalNumberOfVariables; i++) {
            variableArray[i] = bdd.createVar();
        }

        // Step 2-b: Declare and generate the set of plant transitions and controller 
        // transitions with initial value equals FALSE.
        int plantTransition = bdd.getZero();
        int controllerTransition = bdd.getZero();

        for (VertexEdgeSet vertexEdgeSet : gameArena.vertexList) {
            for (EdgeElement edge : vertexEdgeSet.edgeSet) {

                int transition = bdd.getOne();

                char[] sbits = padZeroToString(Integer.toBinaryString(vertexEdgeSet.getVertexID()), NUM_OF_BITS_FOR_STATE).toCharArray();
                for (int j = 0; j < NUM_OF_BITS_FOR_STATE; j++) {
                    if (sbits[j] == '1') {
                        transition = bdd.andTo(transition, variableArray[pre(j)]);
                    } else {
                        transition = bdd.andTo(transition, bdd.not(variableArray[pre(j)]));
                    }
                }

                char[] dbits = padZeroToString(Integer.toBinaryString(edge.getDestVertexID()), NUM_OF_BITS_FOR_STATE).toCharArray();
                for (int j = 0; j < NUM_OF_BITS_FOR_STATE; j++) {
                    if (dbits[j] == '1') {
                        transition = bdd.andTo(transition, variableArray[post(j)]);
                    } else {
                        transition = bdd.andTo(transition, bdd.not(variableArray[post(j)]));
                    }
                }

                if (vertexEdgeSet.getVertexProperty() == VertexEdgeSet.INITIAL_PLANT || vertexEdgeSet.getVertexProperty() == VertexEdgeSet.NONINITIAL_PLANT) {
                    plantTransition = bdd.orTo(plantTransition, transition);
                } else {
                    controllerTransition = bdd.orTo(controllerTransition, transition);
                }
                bdd.deref(transition);
            }
        }

        // Step 2-c: Define variable substitution sequence (permutation)

        int[] p1 = new int[NUM_OF_BITS_FOR_STATE];
        int[] p2 = new int[NUM_OF_BITS_FOR_STATE];
        for (int i = 0; i < NUM_OF_BITS_FOR_STATE; i++) {
            p1[i] = variableArray[pre(i)];
            p2[i] = variableArray[post(i)];
        }


        Permutation perm = bdd.createPermutation(p1, p2);
        Permutation permForward = bdd.createPermutation(p2, p1);

        // Step 2-d: Define the cube to remove x_plum, y_plum, z_plum using the
        // existential quantifier (result only with x, y, z)
        int cube = bdd.getOne();
        int cubeForward = bdd.getOne();
        for (int i = 0; i < NUM_OF_BITS_FOR_STATE; i++) {
            // cube = bdd.andTo(cube, variableArray[START_OF_VERTEX_INDEX_POST + i]);
            cube = bdd.andTo(cube, variableArray[post(i)]);
            cubeForward = bdd.andTo(cubeForward, variableArray[pre(i)]);
        }


        // Step 3-a: Generate the set of initial states: (1, {1})
        // This should be examined by checking all vertices with .
        int initialCondition = bdd.getZero();
        int initialVertexId = -1;
        for (VertexEdgeSet vertexEdgeSet : gameArena.vertexList) {
            if (vertexEdgeSet.getVertexProperty() == VertexEdgeSet.INITIAL_CONTROL || vertexEdgeSet.getVertexProperty() == VertexEdgeSet.INITIAL_PLANT) {

                char[] sbits = padZeroToString(Integer.toBinaryString(vertexEdgeSet.getVertexID()), NUM_OF_BITS_FOR_STATE).toCharArray();
                int s = bdd.getOne();
                for (int j = 0; j < NUM_OF_BITS_FOR_STATE; j++) {
                    if (sbits[j] == '1') {
                        s = bdd.andTo(s, variableArray[pre(j)]);
                    } else {
                        s = bdd.andTo(s, bdd.not(variableArray[pre(j)]));
                    }
                }

                initialVertexId = vertexEdgeSet.getVertexID();
                initialCondition = bdd.orTo(initialCondition, s);
                bdd.deref(s);
            }
        }

        // Step 4: Read the specification and invoke suitable verification engine.

        // Step 4-a: Generate the Goal condition: One set of final states.
        int finalStates = bdd.getZero();
        for (Integer integer : finalEnvVertices) {

            char[] sbits = padZeroToString(Integer.toBinaryString(integer.intValue()), NUM_OF_BITS_FOR_STATE).toCharArray();
            int state = bdd.getOne();
            for (int j = 0; j < NUM_OF_BITS_FOR_STATE; j++) {
                if (sbits[j] == '1') {
                    state = bdd.andTo(state, variableArray[pre(j)]);
                } else {
                    state = bdd.andTo(state, bdd.not(variableArray[pre(j)]));
                }
            }

            finalStates = bdd.orTo(finalStates, state);
        }

        // Step 4-b: Invoke the synthesis engine.
        if (proveExistence) {
            strategy = findWinningStrategyBuechi(finalStates, initialCondition, controllerTransition, plantTransition, perm, cube);
            strategy = bdd.andTo(strategy, controllerTransition);
        } else {
            // To prove the non-existence, we need to switch the role of plant and control 
            strategy = findWinningStrategyBuechi(finalStates, initialCondition, plantTransition, controllerTransition, perm, cube);
        }


        // Step 5: Interpret the strategy (and being back to the caller if needed):

        if (proveExistence == false) {
            MealyMachine machine = new MealyMachine();
            if (strategy == bdd.getZero()) {
                // unable to find a counter-witness
                machine.setSolution(false);
            } else {
                // a counter-witness found
                machine.setSolution(true);
            }
            return machine;
        }

        // Prune the strategy by only considering edges which are led from initial states.
        int totalTransition = bdd.ref(bdd.or(strategy, plantTransition));
        int preImage = bdd.ref(initialCondition);
        int postImage = bdd.getZero();
        do {
            postImage = bdd.orTo(postImage, bdd.replace(bdd.relProd(preImage, totalTransition, cubeForward), permForward));
            if (bdd.biimp(preImage, postImage) == bdd.getOne()) {
                break;
            }
            preImage = bdd.ref(postImage);
            bdd.deref(postImage);
        } while (true);
        strategy = bdd.andTo(strategy, postImage);
        bdd.deref(preImage);
        bdd.deref(postImage);
        bdd.deref(totalTransition);

        // Process the strategy to the specified output format
        PrintStream out = System.out;

        ByteArrayOutputStream barray = new ByteArrayOutputStream();
        PrintStream printStreamByteArray = new PrintStream(barray);
        System.setOut(printStreamByteArray);

        bdd.printSet(strategy);
        String strategyStringFormat = barray.toString();

        // Redirect the output stream back to console again.
        System.setOut(out);

        return generateMealyMachineBuechi(strategyStringFormat, initialVertexId, gameArena);

    }
    
    public void assumptionLearning(ArrayList<AssumptionCandidate> assumptionCandidates, ArrayList<String> inputVariables,
            ArrayList<String> outputVariables){
        //init
        int i;
        ArrayList<String> initialVectorList = new ArrayList<String>();
        initialVectorList.add("");
        ArrayList<String> inputBitVectors = generateBitVectors(0, inputVariables.size(), initialVectorList);
        initialVectorList = new ArrayList<String>();
        initialVectorList.add("");
        ArrayList<String> outputBitVectors = generateBitVectors(0, outputVariables.size(), initialVectorList);        

        printSafetyGameFromCoBuechi(lastSafetyGameArena,inputBitVectors,outputBitVectors);
        //label critical env strategy by backward BFS
        boolean existNewLevel=true;
        Integer safetyLevel=0;
        lastSafetyGameArena.get(1).safetyLevel=safetyLevel;
        lastSafetyGameArena.get(1).isFail=true;
        boolean lastLevelIsEnv=true;
        while(existNewLevel){
            existNewLevel=false;
            safetyLevel=safetyLevel+1;
            for(EquivalenceClass e:lastSafetyGameArena){
                if(!e.isFail){
                    if(!lastLevelIsEnv){ 
                        //focus on env nodes
                        if(e.isEnv){
                            for(String s:inputBitVectors){
                                if(e.successor.get(s).isFail){
                                    e.isFail=true;
                                    e.safetyLevel=safetyLevel;
                                    existNewLevel=true;
                                    break;
                                }                                
                            }
                        }                    
                    }
                    else{
                       //focus on ctrl nodes
                        if(!e.isEnv){
                            boolean isPass=false;
                            for(String s:outputBitVectors){
                                if(!e.successor.get(s).isFail){
                                    isPass=true;
                                    break;
                                }                                
                            }
                            if(!isPass){
                                e.isFail=true;
                                e.safetyLevel=safetyLevel;
                                existNewLevel=true;
                            }
                        }
                    }
                }
            }
            if(lastSafetyGameArena.get(0).isFail){
                existNewLevel=false;
            }
            lastLevelIsEnv=!lastLevelIsEnv;
        }
        //extract the fail path
        ArrayList<String> failPath=new ArrayList<String>();
        EquivalenceClass pivot=lastSafetyGameArena.get(0);
        while(pivot.id!=1){
            if(pivot.isEnv){
                for(String s:inputBitVectors){
                    if(pivot.successor.get(s).isFail && pivot.successor.get(s).safetyLevel.equals(pivot.safetyLevel-1)){
                        pivot=pivot.successor.get(s);
                        failPath.add(s);
                        break;
                    }
                }
            }
            else{
                for(String s:outputBitVectors){
                    if(pivot.successor.get(s).isFail && pivot.successor.get(s).safetyLevel.equals(pivot.safetyLevel-1)){
                        pivot=pivot.successor.get(s);
                        failPath.add(s);
                        break;
                    }                    
                }                
            }
        }
        //print the fail path
        for(i=0;i<failPath.size();i++){
            System.out.print(failPath.get(i)+"-->");
        }
        System.out.print("\n");
    }
    

    
    
    

    
    
    public ArrayList<AssumptionCandidate> listAllAssumptionCandidate(ArrayList<String> inputVariables){
        ArrayList<AssumptionCandidate> assumptionCandidate=new ArrayList<AssumptionCandidate>();
        int i,j,k;
        for(i=0;i<inputVariables.size();i++){
            System.out.print(inputVariables.get(i)+"\n");
        }
        //Template 1 (j=i cause in real case the two signals can be the same one)
        for(i=0;i<inputVariables.size();i++){
            for(j=i;j<inputVariables.size();j++){
                AssumptionCandidate newCandidate=new AssumptionCandidate();
                newCandidate.stringLTL="[] ("+inputVariables.get(i)+" -> X [] "+ inputVariables.get(j)+")";
                newCandidate.type=1;
                newCandidate.variablesArray=new ArrayList<Integer>();
                newCandidate.variablesArray.add(i);
                newCandidate.variablesArray.add(j);
                assumptionCandidate.add(newCandidate);                
                if(i!=j){
                    newCandidate=new AssumptionCandidate();
                    newCandidate.stringLTL="[] ("+inputVariables.get(j)+" -> X [] "+ inputVariables.get(i)+")";
                    newCandidate.type=1;
                    newCandidate.variablesArray=new ArrayList<Integer>();
                    newCandidate.variablesArray.add(j);
                    newCandidate.variablesArray.add(i);
                    assumptionCandidate.add(newCandidate);
                }
            }
        }
        //Template 2 (j=i+1 cause in real case the two signals cannot be the same one)
        for(i=0;i<inputVariables.size();i++){
            for(j=i+1;j<inputVariables.size();j++){
                AssumptionCandidate newCandidate=new AssumptionCandidate();
                newCandidate.stringLTL="[] ("+inputVariables.get(i)+" -> !"+inputVariables.get(j)+")";
                newCandidate.type=2;
                newCandidate.variablesArray=new ArrayList<Integer>();
                newCandidate.variablesArray.add(i);
                newCandidate.variablesArray.add(j);
                assumptionCandidate.add(newCandidate);
            }
        }        
        //Template 3 (j=i, k=j+1)
        for(i=0;i<inputVariables.size();i++){
            for(j=i;j<inputVariables.size();j++){
                for(k=j+1;k<inputVariables.size();k++){
                    AssumptionCandidate newCandidate=new AssumptionCandidate();
                    if(i!=j){                       
                        //i,j,k
                        newCandidate.stringLTL="[] ("+inputVariables.get(i)+" -> X (!"
                                +inputVariables.get(j)+" U "+ inputVariables.get(k) +"))";
                        newCandidate.type=3;
                        newCandidate.variablesArray=new ArrayList<Integer>();
                        newCandidate.variablesArray.add(i);
                        newCandidate.variablesArray.add(j);
                        newCandidate.variablesArray.add(k);
                        assumptionCandidate.add(newCandidate);                        
                        //i,k,j
                        newCandidate.stringLTL="[] ("+inputVariables.get(i)+" -> X (!"
                                +inputVariables.get(k)+" U "+ inputVariables.get(j) +"))";
                        newCandidate.type=3;
                        newCandidate.variablesArray=new ArrayList<Integer>();
                        newCandidate.variablesArray.add(i);
                        newCandidate.variablesArray.add(k);
                        newCandidate.variablesArray.add(j);
                        assumptionCandidate.add(newCandidate);
                        //j,i,k
                        newCandidate.stringLTL="[] ("+inputVariables.get(j)+" -> X (!"
                                +inputVariables.get(i)+" U "+ inputVariables.get(k) +"))";
                        newCandidate.type=3;
                        newCandidate.variablesArray=new ArrayList<Integer>();
                        newCandidate.variablesArray.add(j);
                        newCandidate.variablesArray.add(i);
                        newCandidate.variablesArray.add(k);
                        assumptionCandidate.add(newCandidate);                        
                        //j,k,i
                        newCandidate.stringLTL="[] ("+inputVariables.get(j)+" -> X (!"
                                +inputVariables.get(k)+" U "+ inputVariables.get(i) +"))";
                        newCandidate.type=3;
                        newCandidate.variablesArray=new ArrayList<Integer>();
                        newCandidate.variablesArray.add(j);
                        newCandidate.variablesArray.add(k);
                        newCandidate.variablesArray.add(i);
                        assumptionCandidate.add(newCandidate);
                        //k,i,j
                        newCandidate.stringLTL="[] ("+inputVariables.get(k)+" -> X (!"
                                +inputVariables.get(i)+" U "+ inputVariables.get(j) +"))";
                        newCandidate.type=3;
                        newCandidate.variablesArray=new ArrayList<Integer>();
                        newCandidate.variablesArray.add(k);
                        newCandidate.variablesArray.add(i);
                        newCandidate.variablesArray.add(j);
                        assumptionCandidate.add(newCandidate);                        
                        //k,j,i
                        newCandidate.stringLTL="[] ("+inputVariables.get(k)+" -> X (!"
                                +inputVariables.get(j)+" U "+ inputVariables.get(i) +"))";
                        newCandidate.type=3;
                        newCandidate.variablesArray=new ArrayList<Integer>();
                        newCandidate.variablesArray.add(k);
                        newCandidate.variablesArray.add(j);
                        newCandidate.variablesArray.add(i);
                        assumptionCandidate.add(newCandidate);                        
                    }
                    else{
                        //i,i,k
                        newCandidate.stringLTL="[] ("+inputVariables.get(i)+" -> X (!"
                                +inputVariables.get(i)+" U "+ inputVariables.get(k) +"))";
                        newCandidate.type=3;
                        newCandidate.variablesArray=new ArrayList<Integer>();
                        newCandidate.variablesArray.add(i);
                        newCandidate.variablesArray.add(i);
                        newCandidate.variablesArray.add(k);
                        assumptionCandidate.add(newCandidate); 
                        //k,k,i
                       newCandidate.stringLTL="[] ("+inputVariables.get(k)+" -> X (!"
                                +inputVariables.get(k)+" U "+ inputVariables.get(i) +"))";
                        newCandidate.type=3;
                        newCandidate.variablesArray=new ArrayList<Integer>();
                        newCandidate.variablesArray.add(k);
                        newCandidate.variablesArray.add(k);
                        newCandidate.variablesArray.add(i);
                        assumptionCandidate.add(newCandidate);                         
                    }
                }
            }
        }    
        //Template 4
        for(i=0;i<inputVariables.size();i++){
            AssumptionCandidate newCandidate=new AssumptionCandidate();
            newCandidate.stringLTL="[] ( <> ("+inputVariables.get(i)+"))";
            newCandidate.type=4;
            newCandidate.variablesArray=new ArrayList<Integer>();
            newCandidate.variablesArray.add(i);
            assumptionCandidate.add(newCandidate);            
        }
        return assumptionCandidate;
    } 

    private void printSafetyGameFromCoBuechi(ArrayList<EquivalenceClass> safetyArena,
            ArrayList<String> inputBitVectors, ArrayList<String> outputBitVectors){     
        System.out.print("Start print safety game\n");
        for (EquivalenceClass e: safetyArena){
            System.out.print(e.id+" "+e.isEnv+"\n");
            if(e.successor.size()!=0){
                if(e.isEnv){
                    for(String s:inputBitVectors){
                        System.out.print(s+"->"+e.successor.get(s).id+"\n");
                    }
                }
                else{
                    for(String s:outputBitVectors){
                        System.out.print(s+"->"+e.successor.get(s).id+"\n");
                    }           
                }
            }
        }
    }
    
    
    /**
     * Solve a safety game symbolically and generate a controller (Mealy Machine).
     * 
     * @param safetyArena translated safety game in graph form
     * @param initialVertex initial vertex in the game
     * @param riskVertex risk vertex in the game
     * @param proveExistence prove existence of strategy or prove non-existence by finding a counter-strategy
     * @param isPervasiveStrategy return a non-deterministic machine having all solvers
     * @return MealyMachine as a strategy (having explicit variable to answer a strategy is found)
     */
    private MealyMachine analyzeSafetyGameFromCoBuechi(ArrayList<EquivalenceClass> safetyArena,
            EquivalenceClass initialVertex, EquivalenceClass riskVertex, boolean proveExistence,
            ArrayList<String> inputBitVectors, boolean isPervasiveStrategy) {
        
        bdd.cleanup();

        bdd = new BDD(BDD_MAX_NODE_TABLE_SIZE, BDD_MAX_CACHE_SIZE);

        int plantTransition = bdd.getZero();
        int controllerTransition = bdd.getZero();

        int totalNumberOfVariables = ((int) (Math.ceil(Math.log10(safetyArena.size()) / Math.log10(2)))) * 2;

        int NUM_OF_BITS_FOR_STATE = (int) (Math.ceil(Math.log10(safetyArena.size()) / Math.log10(2)));

        if (NUM_OF_BITS_FOR_STATE == 0) {
            NUM_OF_BITS_FOR_STATE = 1;
            totalNumberOfVariables += 2;
        }

        variableArray = new int[totalNumberOfVariables];
        for (int i = 0; i < totalNumberOfVariables; i++) {
            variableArray[i] = bdd.createVar();
        }


        int initialCondition = bdd.getOne();
        char[] bits = padZeroToString(Integer.toBinaryString(initialVertex.id), NUM_OF_BITS_FOR_STATE).toCharArray();
        for (int j = 0; j < NUM_OF_BITS_FOR_STATE; j++) {
            if (bits[j] == '1') {
                initialCondition = bdd.andTo(initialCondition, variableArray[pre(j)]);
            } else {
                initialCondition = bdd.andTo(initialCondition, bdd.not(variableArray[pre(j)]));
            }
        }

        // long startTime = System.currentTimeMillis();

        // Caching the vertex computation to avoid repeated computation.
        int[] stateIdBDDPre = new int[safetyArena.size()];
        int[] stateIdBDDPost = new int[safetyArena.size()];
        for (int i = 0; i < safetyArena.size(); i++) {

            int sPre = bdd.ref(bdd.getOne());
            int sPost = bdd.ref(bdd.getOne());
            char[] sbits = padZeroToString(Integer.toBinaryString(i), NUM_OF_BITS_FOR_STATE).toCharArray();
            for (int j = 0; j < NUM_OF_BITS_FOR_STATE; j++) {
                if (sbits[j] == '1') {
                    sPre = bdd.andTo(sPre, variableArray[pre(j)]);
                    sPost = bdd.andTo(sPost, variableArray[post(j)]);
                } else {
                    sPre = bdd.andTo(sPre, bdd.not(variableArray[pre(j)]));
                    sPost = bdd.andTo(sPost, bdd.not(variableArray[post(j)]));
                }
            }
            stateIdBDDPre[i] = sPre;
            stateIdBDDPost[i] = sPost;
        }
        // long endTime = System.currentTimeMillis();
        //   System.out.println("Total elapsed time in game creation is :" + (endTime - startTime));


        for (EquivalenceClass source : safetyArena) {

            if (source.isEnv == true) {
                for (EquivalenceClass dest : source.successor.values()) {
                    plantTransition = bdd.orTo(plantTransition, bdd.and(stateIdBDDPre[source.id], stateIdBDDPost[dest.id]));
                }
            } else {
                for (EquivalenceClass dest : source.successor.values()) {
                    controllerTransition = bdd.orTo(controllerTransition, bdd.and(stateIdBDDPre[source.id], stateIdBDDPost[dest.id]));
                }
            }
        }
        // endTime = System.currentTimeMillis();
        //  System.out.println("Total elapsed time in game creation is :" + (endTime - startTime));


        int[] p1 = new int[NUM_OF_BITS_FOR_STATE];
        int[] p2 = new int[NUM_OF_BITS_FOR_STATE];

        for (int i = 0; i < NUM_OF_BITS_FOR_STATE; i++) {
            p1[i] = variableArray[pre(i)];
            p2[i] = variableArray[post(i)];
        }

        Permutation perm = bdd.createPermutation(p1, p2);
        Permutation permForward = bdd.createPermutation(p2, p1);

        int cube = bdd.getOne();
        int cubeForward = bdd.getOne();
        for (int i = 0; i < NUM_OF_BITS_FOR_STATE; i++) {
            cube = bdd.andTo(cube, variableArray[post(i)]);
            cubeForward = bdd.andTo(cubeForward, variableArray[pre(i)]);
        }

        int riskStates = bdd.getOne();
        char[] sbits = padZeroToString(Integer.toBinaryString(riskVertex.id), NUM_OF_BITS_FOR_STATE).toCharArray();
        for (int j = 0; j < NUM_OF_BITS_FOR_STATE; j++) {
            if (sbits[j] == '1') {
                riskStates = bdd.andTo(riskStates, variableArray[pre(j)]);
            } else {
                riskStates = bdd.andTo(riskStates, bdd.not(variableArray[pre(j)]));
            }
        }


        // Invoke the synthesis engine.
        // startTime = System.currentTimeMillis();
        int riskStrategy;
        if (proveExistence) {
            riskStrategy = findWinningStrategySafety(riskStates, initialCondition, controllerTransition, plantTransition, perm, cube);
        } else {
            // For proving non-existence of the controller, we switch the role between environment and control
            riskStrategy = findWinningStrategySafety(riskStates, initialCondition, plantTransition, controllerTransition, perm, cube);
        }

        if (proveExistence == false) {
            MealyMachine machine = new MealyMachine();
            if (riskStrategy == bdd.getOne()) {
                // No counter-witness exists
                machine.setSolution(false);
            } else {
                // Counter-witness exists
                machine.setSolution(true);
                // Here the vertices are used to store input signals that constitute the counter-strategy.
                machine.getVertices().addAll(generateCounterStrategy(safetyArena, plantTransition,
                        controllerTransition, riskStrategy,
                        initialCondition, cubeForward, permForward, new HashSet<String>(), inputBitVectors));

            }
            return machine;
        }

        /*
        int strategy = bdd.ref(bdd.and(controllerTransition, bdd.not(riskStrategy)));
        int totalTransition = bdd.ref(bdd.or(strategy, plantTransition));
        int preImage = bdd.ref(initialCondition);
        int postImage = bdd.getZero();
        do {
        postImage = bdd.orTo(postImage, bdd.replace(bdd.relProd(preImage, totalTransition, cubeForward), permForward));
        if (bdd.biimp(preImage, postImage) == bdd.getOne()) {
        break;
        }
        preImage = bdd.ref(postImage);
        bdd.deref(postImage);
        } while (true);
        strategy = bdd.andTo(strategy, postImage);
        bdd.deref(preImage);
        bdd.deref(postImage);
        bdd.deref(totalTransition);
         * 
         */

        // Redirect the output stream to string, such that we can interpret the printed BDD set for analysis.
        PrintStream out = System.out;

        ByteArrayOutputStream barray = new ByteArrayOutputStream();
        PrintStream printStreamByteArray = new PrintStream(barray);
        System.setOut(printStreamByteArray);
        // bdd.printSet(strategy);
        bdd.printSet(bdd.and(controllerTransition, bdd.not(riskStrategy)));
        String strategyStringFormat = barray.toString();

        // Redirect the output stream back to console again.
        System.setOut(out);

        if (isPervasiveStrategy) {
            return generateMealyMachinePervasiveSafety(strategyStringFormat, initialVertex, safetyArena);
        } else {
            return generateMealyMachineSafety(strategyStringFormat, initialVertex, safetyArena);
        }

    }

    HashSet<String> generateCounterStrategy(ArrayList<EquivalenceClass> safetyArena,
            int plantTransition, int controllerTransition, int riskStrategy,
            int initialCondition, int cubeForward, Permutation permForward,
            HashSet<String> provenExistedInputCombination,
            ArrayList<String> inputCombinations) {

        HashSet<String> result = new HashSet<String>();

        HashMap<String, HashSet<String>> statePossibleActionsMap = new HashMap<String, HashSet<String>>();

        int strategy = bdd.ref(bdd.and(plantTransition, bdd.not(riskStrategy)));

        int totalTransition = bdd.ref(bdd.or(strategy, controllerTransition));
        int preImage = bdd.ref(initialCondition);
        int postImage = bdd.ref(initialCondition);
        do {
            postImage = bdd.orTo(postImage, bdd.replace(bdd.relProd(preImage, totalTransition, cubeForward), permForward));
            if (bdd.biimp(preImage, postImage) == bdd.getOne()) {
                break;
            }
            preImage = bdd.ref(postImage);
            bdd.deref(postImage);
        } while (true);
        strategy = bdd.andTo(strategy, postImage);
        bdd.deref(preImage);
        bdd.deref(postImage);
        bdd.deref(totalTransition);

        // Redirect the output stream to string, such that we can interpret the printed BDD set for analysis.
        PrintStream out = System.out;

        ByteArrayOutputStream barray = new ByteArrayOutputStream();
        PrintStream printStreamByteArray = new PrintStream(barray);
        System.setOut(printStreamByteArray);
        // bdd.printSet(strategy);
        bdd.printSet(strategy);
        String strategyStringFormat = barray.toString();

        // Redirect the output stream back to console again.
        System.setOut(out);

        HashMap<String, String> stateSuccessorStateMap = new HashMap<String, String>();

        String[] lineArray = strategyStringFormat.split("[\\r\\n]");
        for (int i = 0; i < lineArray.length; i++) {
            // Retrieve the source, destination, and the memory content
            if (lineArray[i].length() > 1) {

                StringBuilder sSB = new StringBuilder("");
                StringBuilder dSB = new StringBuilder("");
                for (int j = 0; j < lineArray[i].length(); j++) {
                    if (j % 2 == 0) {
                        sSB.append(lineArray[i].substring(j, j + 1));
                    } else {
                        dSB.append(lineArray[i].substring(j, j + 1));
                    }
                }
                String source = sSB.toString();
                String dest = dSB.toString();

                try {
                    if (source.trim().startsWith("-") || dest.trim().startsWith("-")) {
                        throw new Exception();
                    }

                    int decimalSource = Integer.parseInt(source, 2);
                    int decimalDest = Integer.parseInt(dest, 2);


                    for (String inputValuation : safetyArena.get(decimalSource).successor.keySet()) {
                        if (safetyArena.get(decimalSource).successor.get(inputValuation).id == decimalDest) {
                            if (statePossibleActionsMap.get(String.valueOf(decimalSource)) == null) {
                                statePossibleActionsMap.put(String.valueOf(decimalSource), new HashSet<String>());
                                statePossibleActionsMap.get(String.valueOf(decimalSource)).add(inputValuation);
                            } else {
                                statePossibleActionsMap.get(String.valueOf(decimalSource)).add(inputValuation);
                            }
                            if (Debug.DEBUG) {
                                System.out.println(String.valueOf(decimalSource) + " -" + inputValuation + "->");
                            }
                        }
                    }
                    if (stateSuccessorStateMap.get(String.valueOf(decimalSource)) == null) {
                        stateSuccessorStateMap.put(String.valueOf(decimalSource), String.valueOf(decimalDest));
                    }

                } catch (Exception ex) {
                    // To extract a string with "-" element, then the conversion requires a recursive call.
                    HashSet<String> sourceSet = new HashSet<String>();
                    HashSet<String> destSet = new HashSet<String>();

                    if (source.contains("-")) {
                        sourceSet.addAll(splitVertexFromBDD(source.trim(), 0));
                    } else {
                        sourceSet.add(source);
                    }

                    if (dest.contains("-")) {
                        destSet.addAll(splitVertexFromBDD(dest.trim(), 0));
                    } else {
                        destSet.add(dest);
                    }

                    // Generate all combinations
                    for (String s : sourceSet) {
                        int decimalSource = Integer.parseInt(s, 2);
                        if (decimalSource >= safetyArena.size()) {
                            continue;
                        }
                        for (String d : destSet) {

                            int decimalDest = Integer.parseInt(d, 2);
                            if (decimalDest >= safetyArena.size()) {
                                continue;
                            }

                            for (String inputValuation : safetyArena.get(decimalSource).successor.keySet()) {
                                if (safetyArena.get(decimalSource).successor.get(inputValuation).id == decimalDest) {
                                    if (statePossibleActionsMap.get(String.valueOf(decimalSource)) == null) {
                                        statePossibleActionsMap.put(String.valueOf(decimalSource), new HashSet<String>());
                                        statePossibleActionsMap.get(String.valueOf(decimalSource)).add(inputValuation);
                                    } else {
                                        statePossibleActionsMap.get(String.valueOf(decimalSource)).add(inputValuation);
                                    }
                                    if (Debug.DEBUG) {
                                        System.out.println(String.valueOf(decimalSource) + " -" + inputValuation + "->");
                                    }
                                }
                            }
                            if (stateSuccessorStateMap.get(String.valueOf(decimalSource)) == null) {
                                stateSuccessorStateMap.put(String.valueOf(decimalSource), String.valueOf(decimalDest));
                            }
                        }
                    }
                }
            }
        }

        HashMap<String, HashSet<String>> statePossibleActionsFilterMap = new HashMap<String, HashSet<String>>();
        // Analyze the result by setting 
        for (String state : statePossibleActionsMap.keySet()) {
            if (Collections.disjoint(statePossibleActionsMap.get(state), provenExistedInputCombination)) {
                statePossibleActionsFilterMap.put(state, statePossibleActionsMap.get(state));
            }
        }

        if (statePossibleActionsFilterMap.keySet().isEmpty()) {
            System.out.println("G4LTL: counter-strategy can be fully realized.");
            return result;
        }

        while (true) {

            // Select one input combination that is covered by the largest number of states.
            String candidate = "";
            int coveredNumber = 0;
            for (String sig1 : inputCombinations) {
                if (!result.contains(sig1)) {
                    candidate = sig1;
                    for (String state1 : statePossibleActionsFilterMap.keySet()) {
                        if (statePossibleActionsFilterMap.get(state1).contains(sig1)) {
                            coveredNumber++;
                        }
                    }
                    if (coveredNumber != 0) {
                        break;
                    }
                }
            }

            for (String sig2 : inputCombinations) {
                if (!result.contains(sig2) && !candidate.equals(sig2)) {
                    int tempCoveredNumber = 0;
                    for (String state : statePossibleActionsFilterMap.keySet()) {
                        if (statePossibleActionsFilterMap.get(state).contains(sig2)) {
                            tempCoveredNumber++;
                        }
                    }
                    if (tempCoveredNumber > coveredNumber) {
                        candidate = sig2;
                    }
                }
            }

            // Remove all elements that contains "candidate"
            statePossibleActionsMap = new HashMap<String, HashSet<String>>();
            result.add(candidate);
            for (String state : statePossibleActionsFilterMap.keySet()) {
                if (!statePossibleActionsFilterMap.get(state).contains(candidate)) {
                    statePossibleActionsMap.put(state, statePossibleActionsFilterMap.get(state));
                }
            }
            if (statePossibleActionsMap.keySet().isEmpty()) {
                break;
            } else {
                statePossibleActionsFilterMap = statePossibleActionsMap;
            }

        }

        if (Debug.DEBUG) {
            System.out.println("The minimal set of (unchecked) input valuations that cover all states: " + result.toString());
        }
        return result;

    }

    /**
     * Create the game arena from a Buechi automaton by partitioning input and output signals.
     * 
     * @param inputVariables Input variables
     * @param outputVariables Output variables
     * @param graph Buechi automaton
     * @return the corresponding arena with two players
     */
    private GameArena createGameArena(ArrayList<String> inputVariables, ArrayList<String> outputVariables, Graph graph) {

        // If we need to use aggressive reduction, our heuristic is to select vertices 
        // (other than the initial node) that has the least incoming and outgoing edges.

        if (Debug.DEBUG) {
            Node init = graph.getInit();
            List vertices = graph.getNodes();
            for (Iterator i = vertices.iterator(); i.hasNext();) {
                Node n = (Node) i.next();
                if (init == n) {
                    if (n.getBooleanAttribute("accepting")) {
                        System.out.println("State (init, acc) " + n.getId());
                    } else {
                        System.out.println("State (init) " + n.getId());
                    }
                } else {
                    if (n.getBooleanAttribute("accepting")) {
                        System.out.println("State (acc) " + n.getId());
                    } else {
                        System.out.println("State " + n.getId());
                    }
                }
                for (Iterator j = n.getOutgoingEdges().iterator(); j.hasNext();) {
                    Edge e = (Edge) j.next();
                    System.out.println("\t (" + e.getGuard() + ") -> " + e.getNext().getId());
                }
            }
        }

        ArrayList<Node> vertexList = new ArrayList<Node>();

        // Extract all vertices.      
        List nodes = graph.getNodes();
        for (Iterator i = nodes.iterator(); i.hasNext();) {
            vertexList.add((Node) i.next());
        }

        // Generate all possible bit vectors of the input and outputs
        ArrayList<String> initialVectorList = new ArrayList<String>();
        initialVectorList.add("");
        ArrayList<String> inputBitVectors = generateBitVectors(0, inputVariables.size(), initialVectorList);
        initialVectorList = new ArrayList<String>();
        initialVectorList.add("");
        ArrayList<String> outputBitVectors = generateBitVectors(0, outputVariables.size(), initialVectorList);

        GameArena arena = new GameArena();

        // The ordering of the Buechi automaton follows the index of the
        // vertexList being retrieved. Each index i, it is named in
        // vertexNameArena named "Ei", and stored in the index 
        // i * (size of all possible inputs + 1).       
        vertexNameBuechiAutomaton = new ArrayList<String>();
        // It stores E0, C0_<inputvector1>, ..., E1, C1_<inputvector1>,
        vertexNameArena = new ArrayList<String>();

        // Create the dummy risk vertex which contains a self-loop.


        // Create all environment vertices in the muller arena by extracting from Buechi automata.
        for (Node s : vertexList) {
            vertexNameBuechiAutomaton.add(String.valueOf(s.getId()));
            vertexNameArena.add("E" + String.valueOf(vertexNameBuechiAutomaton.size() - 1));

            VertexEdgeSet vEnv = new VertexEdgeSet();
            int envID = vertexNameArena.size() - 1;
            vEnv.setVertexID(envID);
            if (s.getBooleanAttribute("accepting")) {
                vEnv.setVertexColor(VertexEdgeSet.COLOR_FINAL);
            }
            if (s == graph.getInit()) {
                vEnv.setVertexProperty(VertexEdgeSet.INITIAL_PLANT);
            } else {
                vEnv.setVertexProperty(VertexEdgeSet.NONINITIAL_PLANT);
            }

            // Add the environment vertex
            arena.vertexList.add(vEnv);

            // Create corresponding control vertices with names matching the inputVectors
            for (String vector : inputBitVectors) {
                VertexEdgeSet vCtrl = new VertexEdgeSet();
                vertexNameArena.add("C" + String.valueOf(vertexNameBuechiAutomaton.size() - 1) + "_" + vector);
                vCtrl.setVertexID(vertexNameArena.size() - 1);
                vCtrl.setVertexProperty(VertexEdgeSet.NONINITIAL_CONTROL);
                arena.vertexList.add(vCtrl);
                // Create the environment edge
                EdgeElement edge = new EdgeElement(vEnv.getVertexID(), vCtrl.getVertexID(), vector, 0);
                // Add the edge for the environment                    
                vEnv.edgeSet.add(edge);
            }

        }

        if (Debug.DEBUG) {
            System.out.println("------");
            System.out.println("vertexNameBuechiAutomaton: " + vertexNameBuechiAutomaton.toString());
            System.out.println("vertexNameArena: " + vertexNameArena.toString());
            System.out.println("arena: " + arena.vertexList.size());
        }


        // Create control transitions in the arena: for each edge in the Buechi automaton, 
        // we need to know what is the input (so we can move the the correct control vertex)
        // and what is the output (so we can label the edge with the output).        

        for (Iterator i = nodes.iterator(); i.hasNext();) {
            Node n = (Node) i.next();
            for (Iterator j = n.getOutgoingEdges().iterator(); j.hasNext();) {
                Edge edge = (Edge) j.next();

                ArrayList<String> usedInputBitVectors = new ArrayList<String>();
                ArrayList<String> usedOutputBitVectors = new ArrayList<String>();
                usedInputBitVectors.addAll(inputBitVectors);
                usedOutputBitVectors.addAll(outputBitVectors);

                // Perform normal processing to create edges. The destination is the normal one. 
                String environmentDest = "E" + String.valueOf(vertexNameBuechiAutomaton.indexOf(String.valueOf(edge.getNext().getId())));
                int environmentDestIndex = vertexNameArena.indexOf(environmentDest);

                if (edge.getGuard().equals("-")) {
                    // There is no restriction on the input vectors used.
                } else {
                    StringTokenizer tok = new StringTokenizer(new String(edge.getGuard()), "&");

                    while (tok.hasMoreTokens()) {
                        String token = tok.nextToken();
                        if (token.trim().startsWith("!") && inputVariables.contains(token.trim().substring(1))) {
                            for (String vector : inputBitVectors) {
                                if (vector.substring(inputVariables.indexOf(token.trim().substring(1)),
                                        inputVariables.indexOf(token.trim().substring(1)) + 1).equals("1")) {
                                    // Remove it
                                    usedInputBitVectors.remove(vector);
                                }
                            }
                        } else if (inputVariables.contains(token.trim())) {
                            for (String vector : inputBitVectors) {
                                if (vector.substring(
                                        inputVariables.indexOf(token.trim()), inputVariables.indexOf(token.trim()) + 1).equals("0")) {
                                    // Remove it
                                    usedInputBitVectors.remove(vector);
                                }
                            }
                        } else if (token.trim().startsWith("!") && outputVariables.contains(token.trim().substring(1))) {
                            for (String vector : outputBitVectors) {
                                if (vector.substring(outputVariables.indexOf(token.trim().substring(1)),
                                        outputVariables.indexOf(token.trim().substring(1)) + 1).equals("1")) {
                                    // Remove it
                                    usedOutputBitVectors.remove(vector);
                                }
                            }
                        } else if (outputVariables.contains(token.trim())) {
                            for (String vector : outputBitVectors) {
                                if (vector.substring(
                                        outputVariables.indexOf(token.trim()), outputVariables.indexOf(token.trim()) + 1).equals("0")) {
                                    // Remove it
                                    usedOutputBitVectors.remove(vector);
                                }
                            }
                        }
                    }
                }


                String controlVertexPrefix = "C"
                        + String.valueOf(vertexNameBuechiAutomaton.indexOf(String.valueOf(edge.getSource().getId())));

                for (String input : usedInputBitVectors) {
                    int controlSourceIndex = vertexNameArena.indexOf(controlVertexPrefix + "_" + input);

                    VertexEdgeSet v = arena.vertexList.get(controlSourceIndex);
                    for (String output : usedOutputBitVectors) {
                        // Merge the same destination for the  same output vector. 
                        boolean similarDest = false;
                        for (EdgeElement e : v.edgeSet) {
                            if (e.getDestVertexID()
                                    == environmentDestIndex) { // Append the output to the dest 
                                if (e.getEdgeLabel().contains(output) == false) {
                                    // e.setEdgeLabel(e.getEdgeLabel() + "," + output);
                                    e.getEdgeLabel().add(output);
                                }
                                similarDest = true;
                                break;
                            }
                        }
                        if (similarDest == false) {
                            EdgeElement e = new EdgeElement(controlSourceIndex,
                                    environmentDestIndex, output, 0);
                            v.edgeSet.add(e);
                        }

                    }
                }

            }
        }

        // Printout the translated arena in textural form.
        if (Debug.DEBUG) {
            System.out.println("\n------" + "Buechi/Co-Buechi arena (for output selection)" + "------");
            for (VertexEdgeSet v : arena.vertexList) {
                System.out.println(vertexNameArena.get(v.getVertexID()));
                if (v.getVertexProperty() == VertexEdgeSet.INITIAL_PLANT) {
                    System.out.println("INITIAL");
                }
                for (EdgeElement e : v.edgeSet) {
                    System.out.println("\t" + e.getEdgeLabel() + "-->" + vertexNameArena.get(e.getDestVertexID()));
                }
            }
        }

        return arena;

    }

    /**
     * Find the winning strategy for a Buechi game.
     * 
     * @param finalStates the set of final states
     * @param initialCondition the set of initial states
     * @param controllertransition the set of controller transitions
     * @param planttransition the set of environment transitions
     * @param perm 
     * @param cube 
     * @return index to the bdd for the symbolic startegy
     */
    int findWinningStrategyBuechi(int finalStates, int initialCondition, int controllerTransition, int plantTransition, Permutation perm, int cube) {

        // System.out.println("STEP 1: Calculating recurrence region over final states [Recur(F)]");
        int recurPre = bdd.ref(finalStates);
        int i = 1;
        do {
            int attractorPre = bdd.getZero();
            int j = 1;
            do {
                // [For attractors with controllable locations]
                // Step a1: For ATTR, perform variable swap from x, y, z to x_plum, y_plum, z_plum
                // Step a2: perform AND conjunction with controllertransition to derive set of states
                // Step a3: quantify out x_plum, y_plum, z_plum, and these states are the new attractor ATTR'.

                //int stepa0 = bdd.ref(bdd.exists(bdd.or(attractorPre, recurPre), cube));
                // int stepa1 = bdd.replace(stepa0, perm);
                int stepa1 = bdd.replace(bdd.or(attractorPre, recurPre), perm);
                int stepa2 = bdd.and(stepa1, controllerTransition);
                int stepa3 = bdd.ref(bdd.exists(stepa2, cube));

                int attractorPost_control_state = bdd.ref(stepa3);
                // stream.println("Attractor with control states under processing in step " + j + ":");
                // bdd.printSet(attractorPost_control_state);

                // [For attractors from uncontrollable locations]
                // Step b1: For ATTR, perform variable swap from x, y, z to x_plum, y_plum, z_plum
                // Step b2: For results in step1, perform AND conjunction with planttransition to derive set of states
                // Step b3: quantify out x_plum, y_plum, z_plum, and these states are the new attractor.
                // Step b4: For these states, we "must" make sure that they do not have any transition which leads
                // regions outside the attractor.
                // Step b5: For S\ATTR, perform variable swap from x, y, z to x_plum, y_plum, z_plum
                // Step b6: For results in step5, perform AND conjunction with planttransition to derive set of states
                // Step b7: quantify out x_plum, y_plum, z_plum
                // Step b8: Perform set difference {Step3}\{Step7}, then states in {Step3}\{Step7} will be guaranteed to
                // have EVERY transition leading to the attractor.

                // int stepb0 = bdd.ref(bdd.exists(bdd.or(attractorPre, recurPre), cube));
                // int stepb1 = bdd.ref(bdd.replace(stepb0, perm));
                int stepb1 = bdd.ref(bdd.replace(bdd.or(attractorPre, recurPre), perm));
                int stepb2 = bdd.ref(bdd.and(stepb1, plantTransition));
                int stepb3 = bdd.ref(bdd.exists(stepb2, cube));

                int step = bdd.ref(bdd.not(bdd.or(attractorPre, recurPre))); // S\ATTR
                int stepb5_0 = bdd.ref(bdd.exists(step, cube));
                int stepb5 = bdd.ref(bdd.replace(stepb5_0, perm));
                int stepb6 = bdd.ref(bdd.and(stepb5, plantTransition));
                int stepb7 = bdd.ref(bdd.exists(stepb6, cube));
                int attractorPost_plant_state = bdd.and(stepb3, bdd.not(stepb7));

                // Generate the attractor
                int attractorPost = bdd.ref(bdd.or(attractorPre, bdd.or(attractorPost_control_state, attractorPost_plant_state)));

                // Remove all unused BDD
                // bdd.deref(stepa0);
                bdd.deref(stepa1);
                bdd.deref(stepa2);
                bdd.deref(stepa3);
                bdd.deref(attractorPost_control_state);

                // bdd.deref(stepb0);
                bdd.deref(stepb1);
                bdd.deref(stepb2);
                bdd.deref(stepb3);
                bdd.deref(step);
                bdd.deref(stepb5_0);
                bdd.deref(stepb5);
                bdd.deref(stepb6);
                bdd.deref(stepb7);
                bdd.deref(attractorPost_plant_state);

                // Check if the set of attractors saturates
                if (bdd.ref(bdd.biimp(attractorPre, attractorPost)) == bdd.getOne()) {
                    // System.out.println("------ Finish calculating the attractor (winning region) ----------");
                    // System.out.println("------ Printing the attractor ----------");
                    // bdd.printSet(attractorPost);
                    break;

                } else {
                    j++;
                    bdd.deref(attractorPre); // Dereference the previous image
                    attractorPre =
                            bdd.ref(attractorPost); // Assign the post to be the newly generated image
                    // bdd.printSet(attractorPre);

                    bdd.deref(attractorPost);
                    // System.out.println("-------------------------------------");
                }

            } while (true);

            // Here attractorPre = Attr(recurPre);
            // Intersect with the set of final states
            int recurPost = bdd.ref(bdd.and(finalStates, attractorPre));
            if (bdd.ref(bdd.biimp(recurPre, recurPost)) == bdd.getOne()) {
                // System.out.println("------ Finish calculating the recurrence region ----------");
                // System.out.println("------ Printing the recurrence region ----------");
                // bdd.printSet(bdd.exists(recurPre, cube));
                break;

            } else {
                i++;
                bdd.deref(recurPre); // Dereference the previous image
                recurPre = bdd.ref(recurPost); // Assign the post to be the newly generated image
                bdd.deref(recurPost);
            }

        } while (true);

        if (recurPre == bdd.getZero()) {
            return bdd.getZero();
        }
        // System.out.println("STEP 2: Calculating the attractor over the recurrence region [Attr(Recur(F))]");
        // bdd.printSet(recurPre);

        int attractorPre = bdd.ref(recurPre);
        int controllerSynthesisStrategy = bdd.getZero();

        i = 1;
        do {

            // [For attractors with controllable locations]
            // Step a1: For ATTR, perform variable swap from x, y, z to x_plum, y_plum, z_plum
            // Step a2: perform AND conjunction with controllertransition to derive set of states
            // Step a3: quantify out x_plum, y_plum, z_plum, and these states are the new attractor ATTR'.

            // int stepa0 = bdd.ref(bdd.exists(attractorPre, cube));
            // int stepa1 = bdd.replace(stepa0, perm);
            int stepa1 = bdd.replace(attractorPre, perm);
            int stepa2 = bdd.and(stepa1, controllerTransition);

            if (i == 1) {
                controllerSynthesisStrategy = bdd.orTo(controllerSynthesisStrategy, stepa2);
            } else {
                int stepNew1 = bdd.ref(bdd.and(controllerSynthesisStrategy, stepa2));
                if (bdd.ref(stepNew1) == bdd.getZero()) {
                    //System.out.println("GAVS+: There is something wierd here.");
                }
                int stepNew2 = bdd.ref(bdd.exists(stepNew1, cube));
                int stepNew3 = bdd.ref(bdd.and(controllerSynthesisStrategy, bdd.not(stepNew2)));
                int stepNew4 = bdd.ref(bdd.and(stepa2, bdd.not(stepNew2)));
                bdd.deref(controllerSynthesisStrategy);

                controllerSynthesisStrategy =
                        bdd.or(stepNew3, bdd.or(stepNew4, stepNew1));
                // System.out.println("stepNew5");
                // bdd.printSet(stepNew4);
            }

            int stepa3 = bdd.ref(bdd.exists(stepa2, cube));

            int attractorPost_control_state = bdd.ref(stepa3);
            // System.out.println("Attractor with control states under processing in step " + i + ":");
            // bdd.printSet(attractorPost_control_state);

            // [For attractors from uncontrollable locations]
            // Step b1: For ATTR, perform variable swap from x, y, z to x_plum, y_plum, z_plum
            // Step b2: For results in step1, perform AND conjunction with planttransition to derive set of states
            // Step b3: quantify out x_plum, y_plum, z_plum, and these states are the new attractor.
            // Step b4: For these states, we "must" make sure that they do not have any transition which leads regions
            // outside the attractor.
            // Step b5: For S\ATTR, perform variable swap from x, y, z to x_plum, y_plum, z_plum
            // Step b6: For results in step5, perform AND conjunction with planttransition to derive set of states
            // Step b7: quantify out x_plum, y_plum, z_plum
            // Step b8: Perform set difference {Step3}\{Step7}, then states in {Step3}\{Step7} will be guaranteed to
            // have EVERY transition leading to the attractor.

            // int stepb0 = bdd.ref(bdd.exists(attractorPre, cube));
            // int stepb1 = bdd.replace(stepb0, perm);
            int stepb1 = bdd.replace(attractorPre, perm);
            int stepb2 = bdd.and(stepb1, plantTransition);
            int stepb3 = bdd.ref(bdd.exists(stepb2, cube));

            int step = bdd.not(attractorPre); // S\ATTR
            int stepb5_0 = bdd.ref(bdd.exists(step, cube));
            int stepb5 = bdd.replace(stepb5_0, perm);
            int stepb6 = bdd.and(stepb5, plantTransition);
            int stepb7 = bdd.ref(bdd.exists(stepb6, cube));
            int attractorPost_plant_state = bdd.and(stepb3, bdd.not(stepb7));
            // stream.println("Attractor with plant states under processing in step " + i + ":");
            // bdd.printSet(attractorPost_plant_state);

            // Generate the attractor
            int attractorPost = bdd.or(attractorPre, bdd.or(attractorPost_control_state, attractorPost_plant_state));

            // Remove all unused BDD
            // bdd.deref(stepa0);
            bdd.deref(stepa1);
            bdd.deref(stepa2);
            bdd.deref(stepa3);
            bdd.deref(attractorPost_control_state);

            // bdd.deref(stepb0);
            bdd.deref(stepb1);
            bdd.deref(stepb2);
            bdd.deref(stepb3);
            bdd.deref(step);
            bdd.deref(stepb5_0);
            bdd.deref(stepb5);
            bdd.deref(stepb6);
            bdd.deref(stepb7);
            bdd.deref(attractorPost_plant_state);

            // Check if the set of attractors saturates
            if (bdd.ref(bdd.biimp(attractorPre, attractorPost)) == bdd.getOne()) {
                // System.out.println("------ Finish calculating the attractor (winning region) ----------");

                // System.out.println("Do again the controller part to ensure outgoing edge from recur states");
                int stepa0 = bdd.ref(bdd.exists(attractorPre, cube));
                stepa1 = bdd.replace(stepa0, perm);
                stepa2 = bdd.and(stepa1, controllerTransition);


                int stepNew1 = bdd.ref(bdd.and(controllerSynthesisStrategy, stepa2));
                if (bdd.ref(stepNew1) == bdd.getZero()) {
                    System.out.println("Focus: There are something wierd here.");
                }
                int stepNew2 = bdd.ref(bdd.exists(stepNew1, cube)); // K
                int stepNew3 = bdd.ref(bdd.and(controllerSynthesisStrategy, bdd.not(stepNew2)));
                int stepNew4 = bdd.ref(bdd.and(stepa2, bdd.not(stepNew2)));
                bdd.deref(controllerSynthesisStrategy);

                controllerSynthesisStrategy = bdd.or(stepNew3, bdd.or(stepNew4, stepNew1));

                if (bdd.and(attractorPost, initialCondition) != bdd.getZero()) {
                    // System.out.println("Controller exists");
                } else {
                    // System.out.println("Controller does not exist");
                    return bdd.getZero();
                }

                break;
            } else {
                i++;
                bdd.deref(attractorPre); // Dereference the previous image
                attractorPre = bdd.ref(attractorPost); // Assign the post to be the newly generated image
                bdd.deref(attractorPost);
                // System.out.println("-------------------------------------");
            }

        } while (true);

        return controllerSynthesisStrategy;

    }

    /**
     * Find the winning strategy for a safety game.
     * 
     * @param riskRegion the set of risk states
     * @param controllertransition the set of controllable transitions
     * @param planttransition the set of noncontrollable transitions
     * @param perm
     * @param cube
     * @return The set of control transitions which lead to risk states. 
     */
    int findWinningStrategySafety(int riskRegion, int initialCondition, int controllertransition, int planttransition,
            Permutation perm, int cube) {
        // Here we implement the attractor generator: attractor_{0,i}(Reachability) are the set of states which player 0
        // (controller) can force a visit to Reachability in less or equal to i steps.

        int attractorPre = bdd.ref(riskRegion);
        int controllerRiskSynthesisStrategy = bdd.getZero();

        int i = 1;
        do {

            // [For attractors with noncontrollable locations]
            // Step a1: For ATTR, perform variable swap from x, y, z to x_plum, y_plum, z_plum
            // Step a2: perform AND conjunction with controllertransition to derive set of states
            // Step a3: quantify out x_plum, y_plum, z_plum, and these states are the new attractor ATTR'.

            int stepa1 = bdd.replace(attractorPre, perm);
            int stepa2 = bdd.and(stepa1, planttransition);
            int stepa3 = bdd.ref(bdd.exists(stepa2, cube));
            int attractorPost_plant_state = bdd.ref(stepa3);

            // [For attractors from controllable locations]
            // Step b1: For ATTR, perform variable swap from x, y, z to x_plum, y_plum, z_plum
            // Step b2: For results in step1, perform AND conjunction with planttransition to derive set of states
            // Step b3: quantify out x_plum, y_plum, z_plum, and these states are the new attractor.
            // Step b4: For these states, we "must" make sure that they do not have any transition which leads regions
            //          outside the attractor.
            // Step b5: For S\ATTR, perform variable swap from x, y, z to x_plum, y_plum, z_plum
            // Step b6: For results in step5, perform AND conjunction with controllertransition to derive set of states
            // Step b7: quantify out x_plum, y_plum, z_plum
            // Step b8: Perform set difference {Step3}\{Step7}, then states in {Step3}\{Step7} will be guaranteed
            //          to have EVERY transition leading to the attractor.

            int stepb1 = bdd.replace(attractorPre, perm);
            int stepb2 = bdd.and(stepb1, controllertransition);
            int stepb3 = bdd.ref(bdd.exists(stepb2, cube));
            int step = bdd.not(attractorPre); // S\ATTR
            int stepb5_0 = bdd.ref(bdd.exists(step, cube));
            int stepb5 = bdd.replace(stepb5_0, perm);
            int stepb6 = bdd.and(stepb5, controllertransition);
            int stepb7 = bdd.ref(bdd.exists(stepb6, cube));
            int attractorPost_control_state = bdd.and(stepb3, bdd.not(stepb7));

            // Generate the attractor
            int attractorPost = bdd.or(attractorPre, bdd.or(attractorPost_control_state, attractorPost_plant_state));

            // Remove all unused BDD
            bdd.deref(stepa1);
            bdd.deref(stepa2);
            bdd.deref(stepa3);
            bdd.deref(attractorPost_plant_state);

            bdd.deref(stepb1);
            bdd.deref(stepb2);
            bdd.deref(stepb3);
            bdd.deref(step);
            bdd.deref(stepb5_0);
            bdd.deref(stepb5);
            bdd.deref(stepb6);
            bdd.deref(stepb7);
            bdd.deref(attractorPost_control_state);

            // Check if the set of attractors saturates
            if (bdd.ref(bdd.biimp(attractorPre, attractorPost)) == bdd.getOne()) {
                if (bdd.and(attractorPre, initialCondition) != bdd.getZero()) {
                    // Return that all strategies are risky.
                    return bdd.getOne();
                }
                // System.out.println("------ Finish calculating the attractor (losing region) ----------");
                break;

            } else {
                i++;
                bdd.deref(attractorPre); // Dereference the previous image
                // Assign the post to be  the newly generated image
                attractorPre = bdd.ref(attractorPost);
                bdd.deref(attractorPost);

            }

        } while (true);

        // Once the attractor has been decided, we perform a post-processing.
        // Based on the attractor of the set of reachable states, we perform again the reachability analysis.
        // If there exists any thansition which leads to these states, we put them back to the strategy,
        // as we know that these transitions should never be performed.

        int stepa0 = bdd.ref(bdd.exists(attractorPre, cube));
        int stepa1 = bdd.replace(stepa0, perm);
        int stepa2 = bdd.and(stepa1, controllertransition);

        controllerRiskSynthesisStrategy =
                bdd.orTo(controllerRiskSynthesisStrategy, stepa2);

        controllerRiskSynthesisStrategy =
                bdd.orTo(controllerRiskSynthesisStrategy, bdd.and(riskRegion, controllertransition));

        return controllerRiskSynthesisStrategy;
    }

    private MealyMachine generateMealyMachineBuechi(String strategyStringFormat, int initialVertexId, GameArena gameArena) {


        MealyMachine machine = new MealyMachine();

        if (strategyStringFormat.trim().startsWith("FALSE")) {
            machine.setSolution(false);
            return machine;
        } else {


            String initialID = vertexNameArena.get(initialVertexId).substring(1);

            String[] lineArray = strategyStringFormat.split("[\\r\\n]");

            for (int i = 0; i < lineArray.length; i++) {
                // Retrieve the source, destination, and the memory content
                if (lineArray[i].length() > 1) {

                    StringBuilder sSB = new StringBuilder("");
                    StringBuilder dSB = new StringBuilder("");
                    for (int j = 0; j < lineArray[i].length(); j++) {
                        if (j % 2 == 0) {
                            sSB.append(lineArray[i].substring(j, j + 1));
                        } else {
                            dSB.append(lineArray[i].substring(j, j + 1));
                        }
                    }
                    String source = sSB.toString();
                    String dest = dSB.toString();

                    try {
                        if (source.trim().startsWith("-") || dest.trim().startsWith("-")) {
                            throw new Exception();
                        }
                        int decimalSource = Integer.parseInt(source, 2);
                        int decimalDest = Integer.parseInt(dest, 2);

                        MealyMachineEdgeElement e = new MealyMachineEdgeElement(
                                vertexNameArena.get(decimalSource).split("_")[0].substring(1),
                                vertexNameArena.get(decimalDest).split("_")[0].substring(1),
                                vertexNameArena.get(decimalSource).split("_")[1],
                                getOutputFromBuechiAction(gameArena, decimalSource, decimalDest));

                        machine.getEdges().add(e);
                        machine.getVertices().add(vertexNameArena.get(decimalSource).split("_")[0].substring(1));

                    } catch (Exception ex) {
                        HashSet<String> sourceSet = new HashSet<String>();
                        HashSet<String> destSet = new HashSet<String>();

                        if (source.contains("-")) {
                            sourceSet.addAll(splitVertexFromBDD(source.trim(), 0));
                        } else {
                            sourceSet.add(source);
                        }

                        if (dest.contains("-")) {
                            destSet.addAll(splitVertexFromBDD(dest.trim(), 0));
                        } else {
                            destSet.add(dest);
                        }

                        // Generate all combinations
                        for (String s : sourceSet) {
                            int decimalSource = Integer.parseInt(s, 2);
                            if (decimalSource >= gameArena.vertexList.size()) {
                                continue;
                            }
                            for (String d : destSet) {

                                int decimalDest = Integer.parseInt(d, 2);
                                if (decimalDest >= gameArena.vertexList.size()) {
                                    continue;
                                }

                                machine.getVertices().add(vertexNameArena.get(decimalSource).split("_")[0].substring(1));

                                MealyMachineEdgeElement e = new MealyMachineEdgeElement(
                                        vertexNameArena.get(decimalSource).split("_")[0].substring(1),
                                        vertexNameArena.get(decimalDest).split("_")[0].substring(1),
                                        vertexNameArena.get(decimalSource).split("_")[1],
                                        getOutputFromBuechiAction(gameArena, decimalSource, decimalDest));

                                machine.getEdges().add(e);

                            }
                        }
                    }
                }
            }

            machine.setInitialVertex(initialID);
            machine.setSolution(true);

            return machine;

        }

    }

    private MealyMachine generateMealyMachineSafety(String strategyStringFormat,
            EquivalenceClass initialVertex, ArrayList<EquivalenceClass> safetyArena) {

        MealyMachine machine = new MealyMachine();
        if (strategyStringFormat.trim().startsWith("FALSE")) {
            machine.setSolution(false);
            return machine;
        }

        HashMap<String, String> stateSuccessorStateMap = new HashMap<String, String>();
        HashMap<String, String> stateActionMap = new HashMap<String, String>();

        String[] lineArray = strategyStringFormat.split("[\\r\\n]");
        for (int i = 0; i < lineArray.length; i++) {
            // Retrieve the source, destination, and the memory content
            if (lineArray[i].length() > 1) {

                StringBuilder sSB = new StringBuilder("");
                StringBuilder dSB = new StringBuilder("");
                for (int j = 0; j < lineArray[i].length(); j++) {
                    if (j % 2 == 0) {
                        sSB.append(lineArray[i].substring(j, j + 1));
                    } else {
                        dSB.append(lineArray[i].substring(j, j + 1));
                    }
                }
                String source = sSB.toString();
                String dest = dSB.toString();

                try {
                    if (source.trim().startsWith("-") || dest.trim().startsWith("-")) {
                        throw new Exception();
                    }

                    int decimalSource = Integer.parseInt(source, 2);
                    int decimalDest = Integer.parseInt(dest, 2);

                    if (stateActionMap.get(String.valueOf(decimalSource)) == null) {
                        stateSuccessorStateMap.put(String.valueOf(decimalSource), String.valueOf(decimalDest));
                        stateActionMap.put(String.valueOf(decimalSource), getOutputFromSafetyAction(safetyArena, decimalSource, decimalDest));
                    }
                    /*else {
                    // Here we prefer existing states over new states. Existing states are in general states
                    // with smaller index
                    if (Integer.parseInt(stateSuccessorStateMap.get(String.valueOf(decimalSource))) < decimalDest) {
                    System.err.println("Multiple action possible!");
                    stateSuccessorStateMap.remove(String.valueOf(decimalSource));
                    stateActionMap.remove(String.valueOf(decimalSource));
                    stateSuccessorStateMap.put(String.valueOf(decimalSource), String.valueOf(decimalDest));
                    stateActionMap.put(String.valueOf(decimalSource), getOutputFromSafetyAction(safetyArena, decimalSource, decimalDest));
                    }
                    }
                     * 
                     */

                } catch (Exception ex) {
                    // To extract a string with "-" element, then the conversion requires a recursive call.
                    HashSet<String> sourceSet = new HashSet<String>();
                    HashSet<String> destSet = new HashSet<String>();

                    if (source.contains("-")) {
                        sourceSet.addAll(splitVertexFromBDD(source.trim(), 0));
                    } else {
                        sourceSet.add(source);
                    }

                    if (dest.contains("-")) {
                        destSet.addAll(splitVertexFromBDD(dest.trim(), 0));
                    } else {
                        destSet.add(dest);
                    }

                    // Generate all combinations
                    for (String s : sourceSet) {
                        int decimalSource = Integer.parseInt(s, 2);
                        if (decimalSource >= safetyArena.size()) {
                            continue;
                        }
                        for (String d : destSet) {

                            int decimalDest = Integer.parseInt(d, 2);
                            if (decimalDest >= safetyArena.size()) {
                                continue;
                            }
                            if (stateActionMap.get(String.valueOf(decimalSource)) == null) {
                                stateSuccessorStateMap.put(String.valueOf(decimalSource), String.valueOf(decimalDest));
                                stateActionMap.put(String.valueOf(decimalSource), getOutputFromSafetyAction(safetyArena, decimalSource, decimalDest));
                            }
                            /*else {
                            // Here we prefer existing states over new states. Existing states are in general states
                            // with smaller index
                            
                            if (Integer.parseInt(stateSuccessorStateMap.get(String.valueOf(decimalSource))) > decimalDest) {
                            System.err.println("Multiple action possible!");
                            stateSuccessorStateMap.remove(String.valueOf(decimalSource));
                            stateActionMap.remove(String.valueOf(decimalSource));
                            stateSuccessorStateMap.put(String.valueOf(decimalSource), String.valueOf(decimalDest));
                            stateActionMap.put(String.valueOf(decimalSource), getOutputFromSafetyAction(safetyArena, decimalSource, decimalDest));
                            }
                            }
                             * 
                             */
                        }
                    }
                }
            }
        }

        machine.setSolution(true);

        HashSet<String> envLocations = new HashSet<String>();
        ArrayList<String> workList = new ArrayList<String>();
        workList.add(String.valueOf(initialVertex.id));
        envLocations.add(String.valueOf(initialVertex.id));

        machine.setInitialVertex(String.valueOf(initialVertex.id));

        while (!workList.isEmpty()) {
            String vertexID = workList.remove(0);
            EquivalenceClass v = safetyArena.get(Integer.parseInt(vertexID));
            machine.getVertices().add(String.valueOf(v.id));

            for (String input : v.successor.keySet()) {
                EquivalenceClass succ = v.successor.get(input);
                MealyMachineEdgeElement e = new MealyMachineEdgeElement(String.valueOf(v.id), stateSuccessorStateMap.get(String.valueOf(succ.id)), input, stateActionMap.get(String.valueOf(succ.id)));

                machine.getEdges().add(e);

                if (envLocations.contains(stateSuccessorStateMap.get(String.valueOf(succ.id))) == false) {
                    workList.add(stateSuccessorStateMap.get(String.valueOf(succ.id)));
                    envLocations.add(stateSuccessorStateMap.get(String.valueOf(succ.id)));
                }
            }
        }

        
       // return generateMachineReachableStates(machine);
        
        return machine;
    }

    private MealyMachine generateDeterministicTransitionsInitialState(String strategyStringFormat, int numberOfInputs, int numberOfOutputs) {
        String[] lineArray = strategyStringFormat.split("[\\r\\n]");

        MealyMachine machine = new MealyMachine();
        HashSet<String> inputPatternHandled = new HashSet<String>();

        for (int i = 0; i < lineArray.length; i++) {
            // Retrieve the source, destination, and the memory content
            if (lineArray[i].length() > 1) {

                StringBuilder sSB = new StringBuilder("");
                StringBuilder dSB = new StringBuilder("");
                String input = lineArray[i].substring(0, numberOfInputs);
                String output = lineArray[i].substring(numberOfInputs, numberOfInputs + numberOfOutputs);

                boolean pre = true;
                for (int j = numberOfInputs + numberOfOutputs; j < lineArray[i].length(); j++) {
                    if (pre) {
                        sSB.append(lineArray[i].substring(j, j + 1));
                        pre = false;
                    } else {
                        dSB.append(lineArray[i].substring(j, j + 1));
                        pre = true;
                    }
                }
                String source = sSB.toString();
                String dest = dSB.toString();

                try {
                    if (source.trim().startsWith("-") || dest.trim().startsWith("-")) {
                        throw new Exception();
                    }

                    int decimalSource = Integer.parseInt(source, 2);
                    int decimalDest = Integer.parseInt(dest, 2);

                    if (!inputPatternHandled.contains(input)) {
                        MealyMachineEdgeElement edge = new MealyMachineEdgeElement(source, dest,
                                input, output);
                        inputPatternHandled.add(input);
                        machine.getEdges().add(edge);
                    }

                } catch (Exception ex) {
                    // To extract a string with "-" element, then the conversion requires a recursive call.
                    HashSet<String> sourceSet = new HashSet<String>();
                    HashSet<String> destSet = new HashSet<String>();

                    if (source.contains("-")) {
                        sourceSet.addAll(splitVertexFromBDD(source.trim(), 0));
                    } else {
                        sourceSet.add(source);
                    }

                    if (dest.contains("-")) {
                        destSet.addAll(splitVertexFromBDD(dest.trim(), 0));
                    } else {
                        destSet.add(dest);
                    }

                    // Generate all combinations
                    for (String s : sourceSet) {
                        // int decimalSource = Integer.parseInt(s, 2);

                        for (String d : destSet) {

                            // int decimalDest = Integer.parseInt(d, 2);                           

                            if (!inputPatternHandled.contains(input)) {
                                MealyMachineEdgeElement edge = new MealyMachineEdgeElement(s, d, input, output);
                                inputPatternHandled.add(input);
                                machine.getEdges().add(edge);
                            }
                        }
                    }
                }
            }
        }
        return machine;
    }

    private MealyMachine generateMealyMachineProductMachines(String strategyStringFormat,
            String initialStateBitStringFormat, int numberOfInputs, int numberOfOutputs) {

        HashSet<String> stateInputSet = new HashSet<String>();

        MealyMachine machine = new MealyMachine();
        if (strategyStringFormat.trim().startsWith("FALSE")) {
            machine.setSolution(false);
            return machine;
        }
        machine.setSolution(true);
        HashSet<String> states = new HashSet<String>();

        // Add initial state in bit vector form
        machine.setInitialVertex(initialStateBitStringFormat);

        String[] lineArray = strategyStringFormat.split("[\\r\\n]");


        for (int i = 0; i < lineArray.length; i++) {
            // Retrieve the source, destination, and the memory content
            if (lineArray[i].length() > 1) {

                StringBuilder sSB = new StringBuilder("");
                StringBuilder dSB = new StringBuilder("");
                String input = lineArray[i].substring(0, numberOfInputs);
                String output = lineArray[i].substring(numberOfInputs, numberOfInputs + numberOfOutputs);

                // Here we should only use a boolean variable, as the code inside the game solver does not work!
                boolean pre = true;
                for (int j = numberOfInputs + numberOfOutputs; j < lineArray[i].length(); j++) {
                    if (pre) {
                        sSB.append(lineArray[i].substring(j, j + 1));
                        pre = false;
                    } else {
                        dSB.append(lineArray[i].substring(j, j + 1));
                        pre = true;
                    }
                }
                String source = sSB.toString();
                String dest = dSB.toString();

                try {
                    if (source.trim().startsWith("-") || dest.trim().startsWith("-")) {
                        throw new Exception();
                    }

                    int decimalSource = Integer.parseInt(source, 2);
                    int decimalDest = Integer.parseInt(dest, 2);

                    if (!stateInputSet.contains(source + "_" + input)) {
                        MealyMachineEdgeElement edge = new MealyMachineEdgeElement(source, dest,
                                input, output);

                        machine.getEdges().add(edge);
                        states.add(source);
                        states.add(dest);

                        stateInputSet.add(source + "_" + input);

                    }
                    /*
                    else {
                    System.err.println("saving 1");
                    }
                     * 
                     */



                } catch (Exception ex) {
                    // To extract a string with "-" element, then the conversion requires a recursive call.
                    HashSet<String> sourceSet = new HashSet<String>();
                    HashSet<String> destSet = new HashSet<String>();

                    if (source.contains("-")) {
                        sourceSet.addAll(splitVertexFromBDD(source.trim(), 0));
                    } else {
                        sourceSet.add(source);
                    }

                    if (dest.contains("-")) {
                        destSet.addAll(splitVertexFromBDD(dest.trim(), 0));
                    } else {
                        destSet.add(dest);
                    }

                    // Generate all combinations
                    for (String s : sourceSet) {

                        if (!stateInputSet.contains(s + "_" + input)) {
                            stateInputSet.add(s + "_" + input);


                            for (String d : destSet) {

                                MealyMachineEdgeElement edge = new MealyMachineEdgeElement(s, d,
                                        input, output);

                                machine.getEdges().add(edge);
                                states.add(s);
                                states.add(d);


                                break;
                            }


                        }
                        /*
                        else {
                        System.err.println("saving 2");
                        }
                        
                         * 
                         */

                    }
                }
            }
        }

        // System.err.println(stateInputSet.toString());
        machine.getVertices().addAll(states);
        
        return generateMachineReachableStates(machine);
//return machine;
      }

    
    private MealyMachine generateMachineReachableStates(MealyMachine machine){
              // Generate the set of reachable states 
        // FIXME: Here the algorithm is not optimized!
        
        HashSet<String> reachable = new HashSet<String>();
        reachable.add(machine.getInitialVertex());
        HashSet<String> reachablePost = new HashSet<String>();
        reachablePost.add(machine.getInitialVertex());

        while (true) {
            for (MealyMachineEdgeElement e : machine.getEdges()) {
                if (reachable.contains( e.getSource())) {
                    reachablePost.add(e.getDest());
                }
            }
            if (reachable.size() == reachablePost.size()) {
                break;
            } else {
                reachable = new HashSet<String>();
                reachable.addAll(reachablePost);

            }

        }
        System.err.println("Total number of reachable states = "+reachable.size());
        System.err.println("Total number of states = "+machine.getVertices().size());
        
        MealyMachine machineReachableState = new MealyMachine();
    
        machineReachableState.setSolution(true);
        machineReachableState.setInitialVertex(machine.getInitialVertex());
        machineReachableState.getVertices().addAll(reachable);
        for(MealyMachineEdgeElement e: machine.getEdges()){
            if(reachable.contains(e.getSource())){
                machineReachableState.getEdges().add(e);
            }
        }
        
        return machineReachableState;

    }
    
    private MealyMachine generateMealyMachinePervasiveSafety(String strategyStringFormat,
            EquivalenceClass initialVertex, ArrayList<EquivalenceClass> safetyArena) {

        MealyMachine machine = new MealyMachine();
        if (strategyStringFormat.trim().startsWith("FALSE")) {
            machine.setSolution(false);
            return machine;
        }

        HashMap<String, HashSet<String>> stateSuccessorStateActionMap = new HashMap<String, HashSet<String>>();

        String[] lineArray = strategyStringFormat.split("[\\r\\n]");
        for (int i = 0; i < lineArray.length; i++) {
            // Retrieve the source, destination, and the memory content
            if (lineArray[i].length() > 1) {

                StringBuilder sSB = new StringBuilder("");
                StringBuilder dSB = new StringBuilder("");
                for (int j = 0; j < lineArray[i].length(); j++) {
                    if (j % 2 == 0) {
                        sSB.append(lineArray[i].substring(j, j + 1));
                    } else {
                        dSB.append(lineArray[i].substring(j, j + 1));
                    }
                }
                String source = sSB.toString();
                String dest = dSB.toString();

                try {
                    if (source.trim().startsWith("-") || dest.trim().startsWith("-")) {
                        throw new Exception();
                    }

                    int decimalSource = Integer.parseInt(source, 2);
                    int decimalDest = Integer.parseInt(dest, 2);

                    if (stateSuccessorStateActionMap.get(String.valueOf(decimalSource)) == null) {
                        HashSet<String> set = new HashSet<String>();
                        stateSuccessorStateActionMap.put(String.valueOf(decimalSource), set);
                    }
                    for (String output : getAllOutputFromSafetyAction(safetyArena, decimalSource, decimalDest)) {
                        stateSuccessorStateActionMap.get(String.valueOf(decimalSource)).add(String.valueOf(decimalDest) + "_" + output);
                    }

                } catch (Exception ex) {
                    // To extract a string with "-" element, then the conversion requires a recursive call.
                    HashSet<String> sourceSet = new HashSet<String>();
                    HashSet<String> destSet = new HashSet<String>();

                    if (source.contains("-")) {
                        sourceSet.addAll(splitVertexFromBDD(source.trim(), 0));
                    } else {
                        sourceSet.add(source);
                    }

                    if (dest.contains("-")) {
                        destSet.addAll(splitVertexFromBDD(dest.trim(), 0));
                    } else {
                        destSet.add(dest);
                    }

                    // Generate all combinations
                    for (String s : sourceSet) {
                        int decimalSource = Integer.parseInt(s, 2);
                        if (decimalSource >= safetyArena.size()) {
                            continue;
                        }
                        for (String d : destSet) {

                            int decimalDest = Integer.parseInt(d, 2);
                            if (decimalDest >= safetyArena.size()) {
                                continue;
                            }
                            if (stateSuccessorStateActionMap.get(String.valueOf(decimalSource)) == null) {
                                HashSet<String> set = new HashSet<String>();
                                stateSuccessorStateActionMap.put(String.valueOf(decimalSource), set);
                            }
                            for (String output : getAllOutputFromSafetyAction(safetyArena, decimalSource, decimalDest)) {
                                stateSuccessorStateActionMap.get(String.valueOf(decimalSource)).add(String.valueOf(decimalDest) + "_" + output);
                            }
                        }
                    }
                }
            }
        }

        machine.setSolution(true);

        HashSet<String> envLocations = new HashSet<String>();
        ArrayList<String> workList = new ArrayList<String>();
        workList.add(String.valueOf(initialVertex.id));
        envLocations.add(String.valueOf(initialVertex.id));

        machine.setInitialVertex(String.valueOf(initialVertex.id));

        while (!workList.isEmpty()) {
            String vertexID = workList.remove(0);
            EquivalenceClass v = safetyArena.get(Integer.parseInt(vertexID));
            machine.getVertices().add(String.valueOf(v.id));

            for (String input : v.successor.keySet()) {
                EquivalenceClass succ = v.successor.get(input);
                for (String destSignal : stateSuccessorStateActionMap.get(String.valueOf(succ.id))) {
                    String dest = destSignal.split("_")[0];
                    String signal = destSignal.split("_")[1];
                    MealyMachineEdgeElement e = new MealyMachineEdgeElement(String.valueOf(v.id), dest, input, signal);
                    machine.getEdges().add(e);

                    if (envLocations.contains(dest) == false) {
                        workList.add(dest);
                        envLocations.add(dest);
                    }
                }
            }
        }

        return machine;
    }


    
    
    /**
     * Generate all possible input or output combinations.
     * 
     * @param currentSize
     * @param size
     * @param bitVectors
     * @return 
     */
    private ArrayList<String> generateBitVectors(int currentSize, int size, ArrayList<String> bitVectors) {
        if (currentSize == size) {
            return bitVectors;
        } else {
            ArrayList<String> newBitVectors = new ArrayList<String>();
            for (String bits : bitVectors) {
                newBitVectors.add(bits + "0");
                newBitVectors.add(bits + "1");
            }
            return generateBitVectors(currentSize + 1, size, newBitVectors);
        }
    }

    /**
     * Extract the output from the game-representation Buechi automaton; used 
     * in the  Buechi game solver.
     * 
     * @param arena
     * @param source
     * @param dest
     * @return 
     */
    private String getOutputFromBuechiAction(GameArena arena, int source, int dest) {
        for (VertexEdgeSet v : arena.vertexList) {
            if (v.getVertexID() == source) {
                for (EdgeElement e : v.edgeSet) {
                    if (e.getDestVertexID() == dest) {
                        return e.getEdgeLabel().iterator().next();
                    }
                }
            }
        }
        return "<NO OUTPUT>";
    }

    /**
     * Extract the output from the generated unrolled safety game; used 
     * in the  Co-Buechi + Safety game solver.
     * 
     * @param safetyGame
     * @param source
     * @param dest
     * @return 
     */
    private String getOutputFromSafetyAction(ArrayList<EquivalenceClass> safetyGame, int source, int dest) {
        EquivalenceClass s = safetyGame.get(source);
        EquivalenceClass d = safetyGame.get(dest);
        for (String output : s.successor.keySet()) {
            if (s.successor.get(output) == d) {
                return output;
            }
        }
        return "<NO OUTPUT>";
    }

    private HashSet<String> getAllOutputFromSafetyAction(ArrayList<EquivalenceClass> safetyGame, int source, int dest) {
        HashSet<String> result = new HashSet<String>();
        EquivalenceClass s = safetyGame.get(source);
        EquivalenceClass d = safetyGame.get(dest);
        for (String output : s.successor.keySet()) {
            if (s.successor.get(output) == d) {
                result.add(output);
            }
        }
        return result;
    }

    /**
     * Generate the controller code for the given LTL specification using the Buechi
     * game solver.
     * 
     * @param prob problem under analysis
     * @param ltl2buechi use LTL2Buchi library as the front-end parser
     * @param outputFormat output format (pseudo, SAL, Ptolemy II)
     * @param proveExistence prove existence or non-existence
     * @return 
     */
    public ResultLTLSynthesis invokeMonolithicBuechiEngine(ProblemDescription prob, boolean ltl2buechi, int outputFormat, boolean proveExistence) {

        try {
            GameArena buchiArena = null;
            long startTime = 0;
            long endTime = 0;

            if (ltl2buechi) {
                // Use pure Java-based translator LTL2Buechi
                startTime = System.currentTimeMillis();
                // Step 1: Use LTL2Buchi to generate the corresponding Buechi automaton representation.
                Graph buchiAutomaton;
                if (proveExistence == true) {
                    buchiAutomaton = LTL2Buchi.translate(prob.getLtlSpecification());
                } else {
                    buchiAutomaton = LTL2Buchi.translate("!(" + prob.getLtlSpecification() + ")");
                }


                endTime = System.currentTimeMillis();
                System.out.println("\nTotal elapsed time in execution of method formulaToBA() is : " + (endTime - startTime));

                startTime = System.currentTimeMillis();
                // Step 2: Generate the arena based on reinterpreting the Buechi automata (from the LTL2BA) and the input/output signals.
                buchiArena = createGameArena(prob.getInputVariables(), prob.getOutputVariables(), buchiAutomaton);
                endTime = System.currentTimeMillis();
                System.out.println("Total elapsed time in execution of method createGameArena() is : " + (endTime - startTime));

            } else {
                // Use pure C-based translator LTL2BA (not supported in this version)
            }

            startTime = System.currentTimeMillis();
            ArrayList<Integer> finalEnvVertices = new ArrayList<Integer>();
            for (VertexEdgeSet v : buchiArena.vertexList) {
                if (v.getVertexColor() == VertexEdgeSet.COLOR_FINAL) {
                    finalEnvVertices.add(Integer.valueOf(v.getVertexID()));
                }
            }

            MealyMachine machine = analyzeBuechiGame(buchiArena, finalEnvVertices, proveExistence);


            if (proveExistence) {
                if (machine.hasSolution() == true) {
                    ResultLTLSynthesis result = new ResultLTLSynthesis();
                    result.setStrategyFound(true);
                    // Generate the output format based on the requirement
                    if (outputFormat == OUTPUT_PSUEDO_CODE) {
                        result.setMessage1(PseudoCodeTemplate.createPsuedoCode(machine, prob, "Buchi solver"));

                    } else if (outputFormat == OUTPUT_SAL) {
                        result.setMessage1(SALTemplate.createSALCode(machine, prob, "Buchi solver"));
                    } else if (outputFormat == OUTPUT_FSM_ACTOR_PTOLEMY) {
                        ArrayList<String> initialVectorList = new ArrayList<String>();
                        initialVectorList.add("");
                        ArrayList<String> inputBitVectors = generateBitVectors(0, prob.getInputVariables().size(), initialVectorList);
                        result.setMessage1(PtolemyTemplate.createPtolemyControllerCode(machine, prob, inputBitVectors));
                    } else {
                        result.setMessage1("Buechi game engine finds the controler, but output format known!");
                    }
                    return result;
                } else {
                    ResultLTLSynthesis result = new ResultLTLSynthesis();
                    result.setStrategyFound(false);
                    result.setMessage1("Buechi game engine unable to find the controler");
                    return result;
                }
            } else {
                if (machine.hasSolution() == true) {
                    ResultLTLSynthesis result = new ResultLTLSynthesis();
                    result.setStrategyFound(true);
                    result.setMessage1("Witness of non-existence found by the Buechi game engine");
                    return result;
                } else {
                    ResultLTLSynthesis result = new ResultLTLSynthesis();
                    result.setStrategyFound(false);
                    result.setMessage1("Buechi game engine unable to find the witness");
                    return result;
                }
            }


        } catch (Exception ex) {
            ex.printStackTrace();
            StringWriter sw = new StringWriter();
            PrintWriter pw = new PrintWriter(sw);
            ex.printStackTrace(pw);
            ResultLTLSynthesis result = new ResultLTLSynthesis();
            result.setStrategyFound(false);
            result.setMessage1(sw.toString());
            return result;
        }
    }

    /**
     * Generate the controller code for the given LTL specification using the 
     * Co-Buechi + safety game solver.
     * 
     * @param prob problem under analysis
     * @param ltl2buechi use LTL2Buchi library as the front-end parser
     * @param outputFormat output format (pseudo, SAL, Ptolemy II)
     * @param proveExistence prove existence or non-existence
     * @return 
     */
    public ResultLTLSynthesis invokeMonolithicCoBuechiEngine(ProblemDescription prob,
            boolean ltl2buechi, int outputFormat, boolean proveExistence) {
        ArrayList<String> initialVectorList = new ArrayList<String>();
        initialVectorList.add("");
        ArrayList<String> inputBitVectors = generateBitVectors(0, prob.getInputVariables().size(), initialVectorList);
        initialVectorList = new ArrayList<String>();
        initialVectorList.add("");
        ArrayList<String> outputBitVectors = generateBitVectors(0, prob.getOutputVariables().size(), initialVectorList);

        try {
            GameArena coBuechiArena = null;
            long startTime = 0;
            long endTime = 0;

            if (ltl2buechi) {
                startTime = System.currentTimeMillis();
                // Step 1: Use LTL2BA to generate the corresponding Buechi automaton representation.
                // Collection<ITransition> buechiAutomatonTransitions = LTL2BA4J.formulaToBA("! (" + prob.getLtlSpecification() + ")");
                Graph coBuechiAutomaton;
                if (proveExistence == true) {
                    coBuechiAutomaton = LTL2Buchi.translate("!(" + prob.getLtlSpecification() + ")");
                } else {
                    coBuechiAutomaton = LTL2Buchi.translate(prob.getLtlSpecification());
                }
                
                endTime = System.currentTimeMillis();
                System.out.println("\nTotal elapsed time in execution of method formulaToBA() is : " + (endTime - startTime));
                                
                if (isEmptyLanguage(coBuechiAutomaton)) {
                    if (proveExistence) {
                        // Create a machine that returns all 0s on all possible inputs
                        MealyMachine machine = new MealyMachine();
                        machine.setInitialVertex("0");
                        for (String input : inputBitVectors) {
                            machine.getEdges().add(new MealyMachineEdgeElement("0", "0", input, outputBitVectors.get(0)));
                        }
                        // Pack the machine to the result
                        ResultLTLSynthesis result = new ResultLTLSynthesis();
                        result.setStrategyFound(true);
                        // Generate the output format based on the requirement
                        if (outputFormat == OUTPUT_SAL) {
                            result.setMessage1(SALTemplate.createSALCode(machine, prob, "CoBuchi+safety solver"));
                        } else if (outputFormat == OUTPUT_PSUEDO_CODE) {
                            result.setMessage1(PseudoCodeTemplate.createPsuedoCode(machine, prob, "CoBuchi+safety solver"));
                        } else if (outputFormat == OUTPUT_FSM_ACTOR_PTOLEMY) {
                            // return PtolemyTemplate.createPtolemyCode(machine, prob);
                            result.setMessage1(PtolemyTemplate.createPtolemyControllerCode(machine, prob, inputBitVectors));
                        } else if (outputFormat == OUTPUT_STRUCTURED_TEXT) {
                            result.setMessage1(StructuredTextTemplate.createSTCode(machine, prob, inputBitVectors, false));
                        } else {
                            result.setMessage1("CoBuechi game engine finds the controler, but output format known!");
                        }
                        return result;
                    } else {
                        ResultLTLSynthesis result = new ResultLTLSynthesis();
                        result.setStrategyFound(true);
                        result.setMessage1("Witness of non-existence found by the Co-Buechi + safety game engine");
                        // Add all input combinations
                        result.getTokenSet().addAll(inputBitVectors);
                        return result;
                    }
                }

                startTime = System.currentTimeMillis();
                // Step 2: Generate the arena based on reinterpreting the Buechi automata (from the LTL2BA) and the input/output signals.
                coBuechiArena = createGameArena(prob.getInputVariables(), prob.getOutputVariables(), coBuechiAutomaton);
                endTime = System.currentTimeMillis();
                System.out.println("Total elapsed time in execution of method createGameArena() is : " + (endTime - startTime));

            } else {
                // Use pure C-based translator LTL2BA (not supported in this version)
            }

            // Step 3: Generate risk states
            ArrayList<Integer> riskStates = new ArrayList<Integer>();
            String initialVertexID = "";
            for (VertexEdgeSet v : coBuechiArena.vertexList) {
                if (v.getVertexColor() == VertexEdgeSet.COLOR_FINAL) {
                    riskStates.add(Integer.valueOf(v.getVertexID()));
                }
                if (v.getVertexProperty() == VertexEdgeSet.INITIAL_PLANT) {
                    initialVertexID = String.valueOf(v.getVertexID());
                }
            }


            // Step 4: Invoke safety game translation 
            startTime = System.currentTimeMillis();
            CoBuechiSafetyReduction reduction = new CoBuechiSafetyReduction(coBuechiArena, riskStates, inputBitVectors.size(),
                    inputBitVectors, outputBitVectors);
            ArrayList<EquivalenceClass> safetyGameArena = reduction.createReductionGraph(initialVertexID, 1,
                    prob.getUnrollSteps() * 2 + 1, MAX_VISIT_COBUECHI_FINAL_STATE, inputBitVectors, outputBitVectors);
            lastSafetyGameArena=safetyGameArena;
            endTime = System.currentTimeMillis();
            System.out.println("Total elapsed time in execution of method createReductionGraph() is: " + (endTime - startTime));
            // Step 5: Execute the safety game engine. 
            startTime = System.currentTimeMillis();
            MealyMachine machine = analyzeSafetyGameFromCoBuechi(safetyGameArena, reduction.initialVertex,
                    reduction.riskVertex, proveExistence, inputBitVectors, false);
            
            
            endTime = System.currentTimeMillis();
            System.out.println("Total elapsed time in execution of method analyzeSafetyGame() is: " + (endTime - startTime));

            if (proveExistence) {
                if (machine.hasSolution() == true) {
                    ResultLTLSynthesis result = new ResultLTLSynthesis();
                    result.setStrategyFound(true);
                    // Generate the output format based on the requirement
                    if (outputFormat == OUTPUT_SAL) {
                        result.setMessage1(SALTemplate.createSALCode(machine, prob, "CoBuchi+safety solver"));
                    } else if (outputFormat == OUTPUT_PSUEDO_CODE) {
                        result.setMessage1(PseudoCodeTemplate.createPsuedoCode(machine, prob, "CoBuchi+safety solver"));
                    } else if (outputFormat == OUTPUT_FSM_ACTOR_PTOLEMY) {
                        // return PtolemyTemplate.createPtolemyCode(machine, prob);
                        result.setMessage1(PtolemyTemplate.createPtolemyControllerCode(machine, prob, inputBitVectors));

                    } else if (outputFormat == OUTPUT_STRUCTURED_TEXT) {
                        result.setMessage1(StructuredTextTemplate.createSTCode(machine, prob, inputBitVectors, false));
                    } else {
                        result.setMessage1("CoBuechi game engine finds the controler, but output format known!");
                    }
                    return result;
                } else {
                    ResultLTLSynthesis result = new ResultLTLSynthesis();
                    result.setStrategyFound(false);
                    result.setMessage1("Co-Buechi + safety game engine unable to find the controler");
                    return result;
                }
            } else {
                if (machine.hasSolution() == true) {
                    ResultLTLSynthesis result = new ResultLTLSynthesis();
                    result.setStrategyFound(true);
                    result.setMessage1("Witness of non-existence found by the Co-Buechi + safety game engine");
                    HashSet<String> set = new HashSet<String>();
                    set.addAll(machine.getVertices());

                    result.setTokenSet(set);
                    return result;
                } else {
                    ResultLTLSynthesis result = new ResultLTLSynthesis();
                    result.setStrategyFound(false);
                    result.setMessage1("Co-Buechi + safety game engine unable to find the witness");
                    return result;
                }
            }

        } catch (Exception ex) {
            ex.printStackTrace();
            StringWriter sw = new StringWriter();
            PrintWriter pw = new PrintWriter(sw);
            ex.printStackTrace(pw);
            ResultLTLSynthesis result = new ResultLTLSynthesis();
            result.setStrategyFound(false);
            result.setMessage1(sw.toString());
            return result;
        }
    }

    /**
     * 
     * @param prob
     * @param ltl2buechi
     * @param outputFormat
     * @param proveExistence
     * @return 
     */
    public ResultLTLSynthesis invokeCompositionalCoBuechiEngine(CompositionalProblemDescription prob,
            boolean ltl2buechi, int outputFormat, boolean proveExistence, boolean isShowStrategy) {

        if (proveExistence == false || prob.getPartialSpecification().size() == 1) {
            // Use monolithic solver
            return invokeMonolithicCoBuechiEngine(prob, ltl2buechi, outputFormat, proveExistence);
        }

        long synthesisStartTime = System.currentTimeMillis();


        ArrayList<MealyMachine> subMachines = new ArrayList<MealyMachine>();
        ArrayList<ProblemDescription> subProblems = new ArrayList<ProblemDescription>();

        for (String partialSpec : prob.getPartialSpecification()) {

            System.out.println("Synthesize controller for partial spec: " + partialSpec);

            // Create subproblems
            ProblemDescription subProb = new ProblemDescription();
            subProb.setLtlSpecification(partialSpec);
            subProb.setUnrollSteps(prob.unrollSteps);
            for (String input : prob.inputVariables) {
                if (partialSpec.contains(input)) {
                    subProb.getInputVariables().add(input);
                }
            }
            if (subProb.inputVariables.isEmpty()) {
                subProb.inputVariables.add(prob.inputVariables.get(0));
            }
            for (String output : prob.outputVariables) {
                if (partialSpec.contains(output)) {
                    subProb.getOutputVariables().add(output);
                }
            }
            if (subProb.outputVariables.isEmpty()) {
                subProb.outputVariables.add(prob.outputVariables.get(0));
            }

            ArrayList<String> initialVectorList = new ArrayList<String>();
            initialVectorList.add("");
            ArrayList<String> inputBitVectors = generateBitVectors(0, subProb.getInputVariables().size(), initialVectorList);
            initialVectorList = new ArrayList<String>();
            initialVectorList.add("");
            ArrayList<String> outputBitVectors = generateBitVectors(0, subProb.getOutputVariables().size(), initialVectorList);



            try {
                GameArena coBuechiArena = null;
                long startTime = 0;
                long endTime = 0;

                if (ltl2buechi) {
                    startTime = System.currentTimeMillis();
                    // Step 1: Use LTL2BA to generate the corresponding Buechi automaton representation.
                    // Collection<ITransition> buechiAutomatonTransitions = LTL2BA4J.formulaToBA("! (" + prob.getLtlSpecification() + ")");
                    Graph coBuechiAutomaton = LTL2Buchi.translate("!(" + partialSpec + ")");

                    if (isEmptyLanguage(coBuechiAutomaton)) {
                        // The solver accepts all languages. One can simply omit the construction.
                        continue;
                    }

                    endTime = System.currentTimeMillis();
                    // System.out.println("\nTotal elapsed time in execution of method formulaToBA() is : " + (endTime - startTime));

                    startTime = System.currentTimeMillis();
                    // Step 2: Generate the arena based on reinterpreting the Buechi automata (from the LTL2BA) and the input/output signals.
                    coBuechiArena = createGameArena(subProb.getInputVariables(), subProb.getOutputVariables(), coBuechiAutomaton);
                    endTime = System.currentTimeMillis();
                    // System.out.println("Total elapsed time in execution of method createGameArena() is : " + (endTime - startTime));

                } else {
                    // Use pure C-based translator LTL2BA (not supported in this version)
                }

                // Step 3: Generate risk states
                ArrayList<Integer> riskStates = new ArrayList<Integer>();
                String initialVertexID = "";
                for (VertexEdgeSet v : coBuechiArena.vertexList) {
                    if (v.getVertexColor() == VertexEdgeSet.COLOR_FINAL) {
                        riskStates.add(Integer.valueOf(v.getVertexID()));
                    }
                    if (v.getVertexProperty() == VertexEdgeSet.INITIAL_PLANT) {
                        initialVertexID = String.valueOf(v.getVertexID());
                    }
                }



                // Step 4: Invoke safety game translation 
                startTime = System.currentTimeMillis();
                CoBuechiSafetyReduction reduction = new CoBuechiSafetyReduction(coBuechiArena, riskStates, inputBitVectors.size(), inputBitVectors, outputBitVectors);
                ArrayList<EquivalenceClass> safetyGameArena = reduction.createReductionGraph(initialVertexID, 1,
                        subProb.getUnrollSteps() * 2 + 1, MAX_VISIT_COBUECHI_FINAL_STATE, inputBitVectors, outputBitVectors);
                endTime = System.currentTimeMillis();
                // System.out.println("Total elapsed time in execution of method createReductionGraph() is: " + (endTime - startTime));

                // Step 5: Execute the safety game engine. 
                startTime = System.currentTimeMillis();
                MealyMachine machine = analyzeSafetyGameFromCoBuechi(safetyGameArena, reduction.initialVertex,
                        reduction.riskVertex, proveExistence, inputBitVectors, true);

                endTime = System.currentTimeMillis();
                // System.out.println("Total elapsed time in execution of method analyzeSafetyGame() is: " + (endTime - startTime));

                if (proveExistence) {
                    if (machine.hasSolution() == true) {
                        subMachines.add(machine);
                        subProblems.add(subProb);
                        // Create product machine from pervasive strategies. If this is not possible, then return unknown.
                        if (Debug.DEBUG) {
                            System.out.println(PseudoCodeTemplate.createPsuedoCode(machine, subProb, "CoBuchi+safety solver"));
                        }
                        // System.out.println(SALTemplate.createSALCode(machine, subProb, "CoBuchi+safety solver"));

                    } else {
                        ResultLTLSynthesis result = new ResultLTLSynthesis();
                        result.setStrategyFound(false);
                        result.setMessage1("Co-Buechi + safety game engine unable to find the "
                                + "controler for sub-specification:\n" + partialSpec);
                        return result;
                    }
                } else {
                    if (machine.hasSolution() == true) {
                        ResultLTLSynthesis result = new ResultLTLSynthesis();
                        result.setStrategyFound(true);
                        result.setMessage1("Witness of non-existence found by the Co-Buechi + safety game engine");
                        HashSet<String> set = new HashSet<String>();
                        set.addAll(machine.getVertices());
                        result.setTokenSet(set);
                        return result;
                    } else {
                        ResultLTLSynthesis result = new ResultLTLSynthesis();
                        result.setStrategyFound(false);
                        result.setMessage1("Co-Buechi + safety game engine unable to find the witness");
                        return result;
                    }
                }

            } catch (Exception ex) {
                ex.printStackTrace();
                StringWriter sw = new StringWriter();
                PrintWriter pw = new PrintWriter(sw);
                ex.printStackTrace(pw);
                ResultLTLSynthesis result = new ResultLTLSynthesis();
                result.setStrategyFound(false);
                result.setMessage1(sw.toString());
                return result;
            }
        }




        System.out.println("Start merging strategies using BDDs");

        MealyMachine machine = symbolicProductMealyMachines(subMachines, subProblems, prob.inputVariables, prob.outputVariables, isShowStrategy);
        ResultLTLSynthesis result = new ResultLTLSynthesis();
        if (machine.hasSolution()) {
            if (!isShowStrategy) {
                result.setStrategyFound(true);
                result.setMessage1("Co-Buechi + safety game engine (compositional) finds the controler.\n"
                        + "[The controller is only stored internally as BDDs without printout]");
                return result;
            } else {

                //  ResultLTLSynthesis result = new ResultLTLSynthesis();
                result.setStrategyFound(true);
                // Generate the output format based on the requirement
                if (outputFormat == OUTPUT_SAL) {
                    result.setMessage1(SALTemplate.createSALCode(machine, prob, "CoBuchi+safety solver [compositional]"));
                } else if (outputFormat == OUTPUT_PSUEDO_CODE) {
                    result.setMessage1(PseudoCodeTemplate.createPsuedoCode(machine, prob, "CoBuchi+safety solver [compositional]"));
                } else if (outputFormat == OUTPUT_FSM_ACTOR_PTOLEMY) {
                    // return PtolemyTemplate.createPtolemyCode(machine, prob);
                    ArrayList<String> initialVectorList = new ArrayList<String>();
                    initialVectorList.add("");
                    ArrayList<String> inputBitVectors = generateBitVectors(0, prob.getInputVariables().size(), initialVectorList);
                    result.setMessage1(PtolemyTemplate.createPtolemyControllerCode(machine, prob, inputBitVectors));
                } else if (outputFormat == OUTPUT_STRUCTURED_TEXT) {
                    ArrayList<String> initialVectorList = new ArrayList<String>();
                    initialVectorList.add("");
                    ArrayList<String> inputBitVectors = generateBitVectors(0, prob.getInputVariables().size(), initialVectorList);
                    result.setMessage1(StructuredTextTemplate.createSTCode(machine, prob, inputBitVectors, true));

                } else {
                    result.setMessage1("CoBuechi [compositional] game engine finds the controler, but output format known!");
                }
                return result;
            }

        } else {
            result.setStrategyFound(false);
            result.setMessage1("Co-Buechi + safety game engine (compositional) unable to find the controler");
        }
        return result;

        //  }

        /*
        
        System.out.println("Create compositional strategy by taking subspec 0");
        MealyMachine machine = subMachines.get(0);
        
        
        
        for (int i = 1; i < subMachines.size(); i++) {
        System.out.println("Create compositional strategy by taking subspec " + i);
        machine = productMealyMachine(machine, subMachines.get(i), inputBitVectors);
        
        // If the initial vertex is still in, then proceed
        if (machine.getVertices().contains(machine.getInitialVertex()) == false) {
        machine.setSolution(false);
        break;
        }
        }
        
        ResultLTLSynthesis result = new ResultLTLSynthesis();
        if (machine.hasSolution()) {
        result.setStrategyFound(true);
        // Generate the output format based on the requirement
        if (outputFormat == OUTPUT_SAL) {
        result.setMessage1(SALTemplate.createSALCode(machine, prob, "CoBuchi+safety solver"));
        } else if (outputFormat == OUTPUT_PSUEDO_CODE) {
        result.setMessage1(PseudoCodeTemplate.createPsuedoCode(machine, prob, "CoBuchi+safety solver"));
        } else if (outputFormat == OUTPUT_FSM_ACTOR_PTOLEMY) {
        // return PtolemyTemplate.createPtolemyCode(machine, prob);
        result.setMessage1(PtolemyTemplate.createPtolemyControllerCode(machine, prob, inputBitVectors));
        } else {
        result.setMessage1("CoBuechi game engine finds the controler, but output format unknown!");
        }
        } else {
        result.setStrategyFound(false);
        result.setMessage1("Co-Buechi + safety game engine (compositional) unable to find the controler");
        
        }
        
        long synthesisEndTime = System.currentTimeMillis();
        System.out.println("\nTotal elapsed time in performing compositional synthesis is : " + (synthesisEndTime - synthesisStartTime) + "\n");
        
        
        return result;
        
         * 
         */

    }

    MealyMachine productMealyMachine(MealyMachine firstMachine, MealyMachine secondMachine, ArrayList<String> inputValuations) {

        MealyMachine resultMachine = new MealyMachine();
        // ArrayList<MealyMachineEdgeElement> allEdges = new ArrayList<MealyMachineEdgeElement>();
        String newInitialVertex = firstMachine.getInitialVertex() + "_" + secondMachine.getInitialVertex();
        resultMachine.setInitialVertex(newInitialVertex);

        // HashMap<String, ArrayList<Integer>> stateInputSummary = new HashMap<String, ArrayList<Integer>>();
        ArrayList<String> allProductVertices = new ArrayList<String>();

        for (String s1 : firstMachine.getVertices()) {
            for (String s2 : secondMachine.getVertices()) {
                resultMachine.getVertices().add(s1 + "_" + s2);
                allProductVertices.add(s1 + "_" + s2);
            }
        }
        byte[][] vertexFullInputResponse = new byte[allProductVertices.size()][inputValuations.size()];

        for (MealyMachineEdgeElement e1 : firstMachine.getEdges()) {
            for (MealyMachineEdgeElement e2 : secondMachine.getEdges()) {
                if (e1.getInput().equals(e2.getInput()) && e1.getOutput().equals(e2.getOutput())) {
                    MealyMachineEdgeElement e = new MealyMachineEdgeElement(e1.getSource() + "_" + e2.getSource(),
                            e1.getDest() + "_" + e2.getDest(), e1.getInput(), e1.getOutput());
                    resultMachine.getEdges().add(e);
                    vertexFullInputResponse[allProductVertices.indexOf(e1.getSource() + "_" + e2.getSource())][inputValuations.indexOf(e1.getInput())]++;
                }
            }
        }

        boolean noVertexDeleted = false;
        while (noVertexDeleted == false) {
            noVertexDeleted = true;
            Iterator<String> iterVertex = resultMachine.getVertices().iterator();
            while (iterVertex.hasNext()) {
                String vertex = iterVertex.next();
                if (isArrayContainZero(vertexFullInputResponse[allProductVertices.indexOf(vertex)])) {
                    noVertexDeleted = false;
                    iterVertex.remove();
                    Iterator<MealyMachineEdgeElement> iter = resultMachine.getEdges().iterator();
                    while (iter.hasNext()) {
                        MealyMachineEdgeElement e = iter.next();
                        if (e.getDest().equals(vertex)) {
                            // Update the vector 
                            vertexFullInputResponse[allProductVertices.indexOf(vertex)][inputValuations.indexOf(e.getInput())]--;
                            iter.remove();
                        } else if (e.getSource().equals(vertex)) {
                            iter.remove();
                        }
                    }
                }
            }
            // Recalculate if any of the remaining vertices should be further removed due to the current removal.
        }
        return resultMachine;
    }

    /* This is used when the number of input bits is excessively large. 
     * We use BDDs to perform corss-product of two automata. 
     * Subsequently, we use the operation bdd.forall() to eliminate variables that does not contain all input combinations.
     * 
     * Notice that for symbolic production, we should not have too many sub-specifications.
     * 
     */
    MealyMachine symbolicProductMealyMachines(ArrayList<MealyMachine> subMachines,
            ArrayList<ProblemDescription> subProblems,
            ArrayList<String> inputVariables, ArrayList<String> outputVariables, boolean isShowStrategy) {

        bdd.cleanup();

        bdd = new BDD(BDD_MAX_NODE_TABLE_SIZE, BDD_MAX_CACHE_SIZE);

        int[] startingIndices = new int[subMachines.size()];
        int[] NUM_OF_BITS_FOR_STATE = new int[subMachines.size()];

        int totalNumberOfVariables = inputVariables.size() + outputVariables.size();
        for (int i = 0; i < subMachines.size(); i++) {
            startingIndices[i] = totalNumberOfVariables;
            totalNumberOfVariables += ((int) (Math.ceil(Math.log10(subMachines.get(i).getVertices().size()) / Math.log10(2)))) * 2;
            NUM_OF_BITS_FOR_STATE[i] = ((int) (Math.ceil(Math.log10(subMachines.get(i).getVertices().size()) / Math.log10(2))));
            // Handle the case where only one variable is there
            if (NUM_OF_BITS_FOR_STATE[i] == 0) {
                NUM_OF_BITS_FOR_STATE[i] += 1;
                totalNumberOfVariables += 2;
            }
        }
        variableArray = new int[totalNumberOfVariables];
        for (int i = 0; i < totalNumberOfVariables; i++) {
            variableArray[i] = bdd.createVar();
        }

        int[] transitions = new int[subMachines.size()];
        for (int i = 0; i < subMachines.size(); i++) {
            transitions[i] = bdd.getZero();

            for (MealyMachineEdgeElement edge : subMachines.get(i).getEdges()) {
                int transition = bdd.getOne();

                char[] sbits = padZeroToString(Integer.toBinaryString(subMachines.get(i).getVertices().indexOf(edge.getSource())), NUM_OF_BITS_FOR_STATE[i]).toCharArray();
                for (int j = 0; j < NUM_OF_BITS_FOR_STATE[i]; j++) {
                    if (sbits[j] == '1') {
                        transition = bdd.andTo(transition, variableArray[startingIndices[i] + pre(j)]);
                    } else {
                        transition = bdd.andTo(transition, bdd.not(variableArray[startingIndices[i] + pre(j)]));
                    }
                }
                // bdd.printSet(transition);

                char[] dbits = padZeroToString(Integer.toBinaryString(subMachines.get(i).getVertices().indexOf(edge.getDest())), NUM_OF_BITS_FOR_STATE[i]).toCharArray();
                for (int j = 0; j < NUM_OF_BITS_FOR_STATE[i]; j++) {
                    if (dbits[j] == '1') {
                        transition = bdd.andTo(transition, variableArray[startingIndices[i] + post(j)]);
                    } else {
                        transition = bdd.andTo(transition, bdd.not(variableArray[startingIndices[i] + post(j)]));
                    }
                }
                // bdd.printSet(transition);

                char[] ibits = edge.getInput().toCharArray();
                for (int j = 0; j < ibits.length; j++) {
                    int actualVariableIndex = inputVariables.indexOf(subProblems.get(i).inputVariables.get(j));
                    if (ibits[j] == '1') {
                        transition = bdd.andTo(transition, variableArray[actualVariableIndex]);
                    } else {
                        transition = bdd.andTo(transition, bdd.not(variableArray[actualVariableIndex]));
                    }
                }
                // bdd.printSet(transition);

                char[] obits = edge.getOutput().toCharArray();
                for (int j = 0; j < obits.length; j++) {
                    int actualVariableIndex = outputVariables.indexOf(subProblems.get(i).outputVariables.get(j));
                    if (obits[j] == '1') {
                        transition = bdd.andTo(transition, variableArray[inputVariables.size() + actualVariableIndex]);
                    } else {
                        transition = bdd.andTo(transition, bdd.not(variableArray[inputVariables.size() + actualVariableIndex]));
                    }
                }
                // bdd.printSet(transition);

                transitions[i] = bdd.orTo(transitions[i], transition);
            }
        }

        int productTransition = bdd.ref(bdd.getOne());
        for (int i = 0; i < subMachines.size(); i++) {
            productTransition = bdd.andTo(productTransition, transitions[i]);
            // System.out.println("Product with submachine " + i);
            // bdd.printSet(productTransition);
        }



        int stateBits = (totalNumberOfVariables - inputVariables.size() - outputVariables.size()) / 2;
        int[] p1 = new int[stateBits];
        int[] p2 = new int[stateBits];
        for (int i = 0; i < stateBits; i++) {
            p1[i] = variableArray[startingIndices[0] + pre(i)];
            p2[i] = variableArray[startingIndices[0] + post(i)];
        }


        Permutation permP1ToP2 = bdd.createPermutation(p1, p2);
        Permutation permP2ToP1 = bdd.createPermutation(p2, p1);


        // exist: use to quantify all output actions and all post values
        int exist = bdd.getOne();
        for (int i = 0; i < outputVariables.size(); i++) {
            exist = bdd.andTo(exist, variableArray[inputVariables.size() + i]);
        }
        for (int i = 0; i < subMachines.size(); i++) {
            for (int j = 0; j < NUM_OF_BITS_FOR_STATE[i]; j++) {
                exist = bdd.andTo(exist, variableArray[startingIndices[i] + post(j)]);
            }
        }
        // System.out.println("exist");
        // bdd.printSet(exist);

        int forall = bdd.getOne();
        for (int i = 0; i < inputVariables.size(); i++) {
            forall = bdd.andTo(forall, variableArray[i]);
        }
        // System.out.println("forall");
        // bdd.printSet(forall);

        // Check if the initial state combination is within
        int init = bdd.getOne();
        StringBuilder initBitPattern = new StringBuilder("");
        for (int i = 0; i < subMachines.size(); i++) {
            char[] sbits = padZeroToString(Integer.toBinaryString(subMachines.get(i).getVertices().indexOf(subMachines.get(i).getInitialVertex())), NUM_OF_BITS_FOR_STATE[i]).toCharArray();
            initBitPattern.append(sbits);
            for (int j = 0; j < NUM_OF_BITS_FOR_STATE[i]; j++) {
                if (sbits[j] == '1') {
                    init = bdd.andTo(init, variableArray[startingIndices[i] + pre(j)]);
                } else {
                    init = bdd.andTo(init, bdd.not(variableArray[startingIndices[i] + pre(j)]));
                }
            }
        }
        // System.out.println("init");
        // bdd.printSet(init);

        int preStrategy = bdd.ref(productTransition);
        int index = 0;
        while (true) {
            System.out.print(index + " ");
            int statesWithoutConsideringOutputDest = bdd.exists(preStrategy, exist);
            // bdd.printSet(statesWithoutConsideringOutputDest);
            int remainingStatesHavingAllInputValues = bdd.forall(statesWithoutConsideringOutputDest, forall);
            //  System.out.println("remainingStatesHavingAllInputValues");
            // bdd.printSet(remainingStatesHavingAllInputValues);
            // System.out.println("post");
            // bdd.printSet(bdd.replace(remainingStatesHavingAllInputValues, permP1ToP2));
            int postStrategy = bdd.and(preStrategy, remainingStatesHavingAllInputValues);
            postStrategy = bdd.andTo(postStrategy, bdd.replace(remainingStatesHavingAllInputValues, permP1ToP2));

            if (preStrategy == postStrategy) {
                break;
            } else {
                preStrategy = bdd.ref(postStrategy);
                index++;
            }
        }
        System.out.println();




        //if (bdd.and(preStrategy, init) == bdd.getZero()) {
        if (bdd.and(preStrategy, init) == bdd.getZero()) {
            // Pack the initial condition back to the synthesis engine.    
            MealyMachine machine = new MealyMachine();
            machine.setSolution(false);
            return machine;

        } else {
            if (!isShowStrategy) {
                MealyMachine machine = new MealyMachine();
                machine.setSolution(true);
                return machine;
            } else {

                // Perform further strategy pruning

                PrintStream out = System.out;
                ByteArrayOutputStream barray = new ByteArrayOutputStream();
                PrintStream printStreamByteArray = new PrintStream(barray);
                System.setOut(printStreamByteArray);
                // bdd.printSet(strategy);
                bdd.printSet(bdd.and(preStrategy, init));
                String initialStateStrategyStringFormat = barray.toString();

                System.setOut(out);

                MealyMachine initialDeterministicTransitions = generateDeterministicTransitionsInitialState(initialStateStrategyStringFormat,
                        inputVariables.size(), outputVariables.size());


                int initDet = bdd.getZero();
                for (MealyMachineEdgeElement edge : initialDeterministicTransitions.getEdges()) {
                    // System.out.println(edge.getSource());
                    int transition = bdd.getOne();

                    char[] sbits = edge.getSource().toCharArray();
                    for (int j = 0; j < sbits.length; j++) {
                        if (sbits[j] == '1') {
                            transition = bdd.andTo(transition, variableArray[startingIndices[0] + pre(j)]);
                        } else if (sbits[j] == '0') {
                            transition = bdd.andTo(transition, bdd.not(variableArray[startingIndices[0] + pre(j)]));
                        }
                    }

                    char[] dbits = edge.getDest().toCharArray();
                    for (int j = 0; j < dbits.length; j++) {
                        if (dbits[j] == '1') {
                            transition = bdd.andTo(transition, variableArray[startingIndices[0] + post(j)]);
                        } else if (dbits[j] == '0') {
                            transition = bdd.andTo(transition, bdd.not(variableArray[startingIndices[0] + post(j)]));
                        }
                    }

                    char[] ibits = edge.getInput().toCharArray();
                    for (int j = 0; j < ibits.length; j++) {
                        if (ibits[j] == '1') {
                            transition = bdd.andTo(transition, variableArray[j]);
                        } else if (ibits[j] == '0') {
                            transition = bdd.andTo(transition, bdd.not(variableArray[j]));
                        }
                    }

                    char[] obits = edge.getOutput().toCharArray();
                    for (int j = 0; j < obits.length; j++) {
                        if (obits[j] == '1') {
                            transition = bdd.andTo(transition, variableArray[inputVariables.size() + j]);
                        } else if (obits[j] == '0') {
                            transition = bdd.andTo(transition, bdd.not(variableArray[inputVariables.size() + j]));
                        }
                    }
                    initDet = bdd.orTo(initDet, transition);
                }

                int finalStrategy = bdd.ref(bdd.or(bdd.and(preStrategy, bdd.not(init)), initDet));




                System.out.println("Start strategy pruning (from initial state; still maintain non-deterministism)");

                int existPruning = bdd.getOne();

                for (int i = 0; i < inputVariables.size(); i++) {
                    existPruning = bdd.andTo(existPruning, variableArray[i]);
                }
                for (int i = 0; i < outputVariables.size(); i++) {
                    existPruning = bdd.andTo(existPruning, variableArray[inputVariables.size() + i]);
                }
                for (int i = 0; i < subMachines.size(); i++) {
                    for (int j = 0; j < NUM_OF_BITS_FOR_STATE[i]; j++) {
                        existPruning = bdd.andTo(existPruning, variableArray[startingIndices[i] + pre(j)]);
                    }
                }

                int preState = bdd.ref(init);
                int i = 0;
                while (true) {
                    System.out.print(i + " ");
                    int postState = bdd.orTo(preState,
                            bdd.replace(bdd.exists(bdd.and(finalStrategy, preState), existPruning), permP2ToP1));
                    // bdd.printSet( bdd.replace(bdd.exists(bdd.and(preStrategy, preState), existPruning), permP2ToP1));
                    if (preState == postState) {
                        break;
                    } else {
                        preState = postState;
                        i++;
                    }
                }
                System.out.println();

                out = System.out;
                barray = new ByteArrayOutputStream();
                printStreamByteArray = new PrintStream(barray);
                System.setOut(printStreamByteArray);
                bdd.printSet(bdd.and(finalStrategy, bdd.and(preState, bdd.replace(preState, permP1ToP2))));
                String strategyStringFormat = barray.toString();

                System.setOut(out);

                return generateMealyMachineProductMachines(strategyStringFormat, initBitPattern.toString(),
                        inputVariables.size(), outputVariables.size());

            }
        }


    }

    boolean isEmptyLanguage(Graph graph) {
        List vertices = graph.getNodes();
        for (Iterator i = vertices.iterator(); i.hasNext();) {
            Node n = (Node) i.next();
            if (n.getBooleanAttribute("accepting")) {
                return false;
            }
        }
        return true;
    }

    boolean isArrayContainZero(byte[] array) {
        for (int num : array) {
            if (num == 0) {
                return true;
            }
        }
        return false;
    }

    /**
     * Invoke the synthesis engine (without a call from the GUI).
     * 
     * @param prob
     * @param isBuechiSolver
     * @return 
     */
    public MealyMachine invokeSynthesisLibrary(ProblemDescription prob, boolean isBuechiSolver, HashSet<String> provenInputs) {
        try {
            Graph buchiAutomaton = LTL2Buchi.translate(prob.getLtlSpecification());
            GameArena buchiArena = createGameArena(prob.getInputVariables(), prob.getOutputVariables(), buchiAutomaton);
            if (isBuechiSolver) {
                ArrayList<Integer> finalEnvVertices = new ArrayList<Integer>();
                for (VertexEdgeSet v : buchiArena.vertexList) {
                    if (v.getVertexColor() == VertexEdgeSet.COLOR_FINAL) {
                        finalEnvVertices.add(Integer.valueOf(v.getVertexID()));
                    }
                }
                return analyzeBuechiGame(buchiArena, finalEnvVertices, true);

            } else {

                // Step 1: Use LTL2BA to generate the corresponding Buechi automaton representation.
                // Collection<ITransition> buechiAutomatonTransitions = LTL2BA4J.formulaToBA("! (" + prob.getLtlSpecification() + ")");
                Graph coBuechiAutomaton = LTL2Buchi.translate("!(" + prob.getLtlSpecification() + ")");

                // Step 2: Generate the arena based on reinterpreting the Buechi automata (from the LTL2BA) and the input/output signals.
                GameArena coBuechiArena = createGameArena(prob.getInputVariables(), prob.getOutputVariables(), coBuechiAutomaton);

                // Step 3: Risk states
                ArrayList<Integer> riskStates = new ArrayList<Integer>();
                String initialVertexID = "";
                for (VertexEdgeSet v : coBuechiArena.vertexList) {
                    if (v.getVertexColor() == VertexEdgeSet.COLOR_FINAL) {
                        riskStates.add(Integer.valueOf(v.getVertexID()));
                    }
                    if (v.getVertexProperty() == VertexEdgeSet.INITIAL_PLANT) {
                        initialVertexID = String.valueOf(v.getVertexID());
                    }
                }

                ArrayList<String> initialVectorList = new ArrayList<String>();
                initialVectorList.add("");
                ArrayList<String> inputBitVectors = generateBitVectors(0, prob.getInputVariables().size(), initialVectorList);
                initialVectorList = new ArrayList<String>();
                initialVectorList.add("");
                ArrayList<String> outputBitVectors = generateBitVectors(0, prob.getOutputVariables().size(), initialVectorList);

                // Step 4: Invoke safety game translation 
                CoBuechiSafetyReduction reduction = new CoBuechiSafetyReduction(coBuechiArena, riskStates, inputBitVectors.size(), inputBitVectors, outputBitVectors);
                ArrayList<EquivalenceClass> safetyGameArena = reduction.createReductionGraph(initialVertexID, 1,
                        prob.getUnrollSteps() * 2 + 1, MAX_VISIT_COBUECHI_FINAL_STATE, inputBitVectors, outputBitVectors);

                // Step 5: Execute the safety game engine. 
                return analyzeSafetyGameFromCoBuechi(safetyGameArena, reduction.initialVertex,
                        reduction.riskVertex, true, inputBitVectors, false);
            }
        } catch (Exception ex) {
            StringWriter sw = new StringWriter();
            PrintWriter pw = new PrintWriter(sw);
            ex.printStackTrace(pw);
            return null;
        }
    }

    /**
     * Padd 0 before a string to a specified length.
     * 
     * @param s
     * @param idealLength
     * @return 
     */
    static String padZeroToString(String s, int specifiedLength) {
        if (s.length() > specifiedLength) {
            System.out.println("Error: the string under padding is longer than the ideal length");
            return s;
        } else {
            StringBuffer zeroString = new StringBuffer("");
            for (int i = 0; i < specifiedLength - s.length(); i++) {
                zeroString.append("0");
            }
            return (zeroString.append(s)).toString();
        }
    }

    private int post(int i) {
        return 2 * i + 1;
    }

    private int pre(int i) {
        return 2 * i;
    }

    /**
     * Print the textural presentation of a Buechi automata; debug only.
     * 
     * @param spec 
     */
    private void printBuechiAutomata(String spec) {

        try {
            Graph graph = LTL2Buchi.translate(spec);
            Node init = graph.getInit();

            List nodes = graph.getNodes();
            for (Iterator i = nodes.iterator(); i.hasNext();) {
                Node n = (Node) i.next();
                if (init == n) {
                    if (init.getBooleanAttribute("accepting")) {
                        System.out.println("State (init, acc) " + init.getId());
                    } else {
                        System.out.println("State (init) " + init.getId());
                    }
                } else {
                    if (n.getBooleanAttribute("accepting")) {
                        System.out.println("State (acc) " + n.getId());
                    } else {
                        System.out.println("State " + n.getId());
                    }
                }
                for (Iterator j = n.getOutgoingEdges().iterator(); j.hasNext();) {

                    Edge e = (Edge) j.next();
                    System.out.println("\t (" + e.getGuard() + ") -> " + e.getNext().getId());
                    String guard = e.getGuard().equals("-") ? "1" : e.getGuard();

                    StringTokenizer tok = new StringTokenizer(new String(guard), "&");
                    guard = "";

                    while (tok.hasMoreTokens()) {
                        guard += tok.nextToken();

                        if (tok.hasMoreTokens()) {
                            guard += " && ";
                        }
                    }

                    tok = new StringTokenizer(new String(guard), "|");
                    guard = "";

                    while (tok.hasMoreTokens()) {
                        guard += tok.nextToken();

                        if (tok.hasMoreTokens()) {
                            guard += " || ";
                        }
                    }
                }
            }

        } catch (Exception ex) {
            ex.printStackTrace();
        }
    }

    /**
     * Analyze the string to know how many vertices are encoded.
     * 
     * @param underProcessing
     * @param lengthIndex
     * @return
     */
    static HashSet<String> splitVertexFromBDD(String underProcessing, int lengthIndex) {
        if (lengthIndex == underProcessing.length()) {
            HashSet<String> returnSet = new HashSet<String>();
            returnSet.add("");
            return returnSet;
        } else {
            if (underProcessing.substring(lengthIndex, lengthIndex + 1).equalsIgnoreCase("-")) {
                HashSet<String> returnSet = new HashSet<String>();
                lengthIndex++;

                HashSet<String> subStringSet = splitVertexFromBDD(underProcessing, lengthIndex);
                for (String str : subStringSet) {
                    returnSet.add("0" + str);
                    returnSet.add("1" + str);
                }

                return returnSet;
            } else {
                HashSet<String> returnSet = new HashSet<String>();
                HashSet<String> subStringSet = splitVertexFromBDD(underProcessing, lengthIndex + 1);
                for (String str : subStringSet) {
                    returnSet.add(underProcessing.substring(lengthIndex, lengthIndex + 1) + str);
                }
                return returnSet;
            }
        }
    }
}

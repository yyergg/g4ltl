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
package g4ltl;

import g4ltl.utility.CompressibilityCheck;
import g4ltl.utility.ProblemDescription;
import g4ltl.utility.PtolemyTemplate;
import g4ltl.utility.ResultLTLSynthesis;
import g4ltl.utility.SynthesisEngine;
import java.awt.GraphicsEnvironment;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import javax.swing.ImageIcon;
import javax.swing.JFileChooser;
import javax.swing.JOptionPane;

/**
 * APIs for all utility functions including file parsing and external invocation
 * of G4LTL without using the GUI.
 * 
 * @author Chihhong Cheng
 * @version 0.3 2013/02/28
 */
public class SolverUtility {

    static ImageIcon G4LTL_ICON = new ImageIcon("G4LTL.png");
    static String LTL = "LTL";
    static String INPUT = "INPUT";
    static String OUTPUT = "OUTPUT";
    static String TIMER = "TIMER";
    static String ASSUME = "ASSUME";
    static int MAX_ASSEMBLY_GUARANTEES = 2;

    public static ImageIcon getIcon() {
        return G4LTL_ICON;
    }

    public static void setMaxGuaranteeGroupedElements(int number) {
        MAX_ASSEMBLY_GUARANTEES = number;
    }

    /*
    public String getOutputMultiplexer() {
    return outputMultiplexer;
    }
     * 
     */
    static String changeSpecToInternalFormat(String spec) {
        spec = spec.replaceAll("ALWAYS", " [] ");
        spec = spec.replaceAll("EVENTUALLY", " <> ");
        spec = spec.replaceAll("UNTIL", " U ");
        spec = spec.replaceAll("NEXT", " X ");
        return spec;
    }

    /**
     * Read from the file and generate the input signals, output signals, and
     * the LTL specification.
     *
     * @param selectedFile the specification file
     * @return input, output, and LTL specification
     * @throws Exception exceptions during the file accessing process.
     */
    static HashMap<String, String> getLTLSpecificationFromFile(File selectedFile) throws Exception {
        HashMap<String, String> map = new HashMap<String, String>();

        StringBuilder ltlSpec = new StringBuilder("");
        StringBuilder inputSpec = new StringBuilder("");
        StringBuilder outputSpec = new StringBuilder("");
        StringBuilder timerSpec = new StringBuilder("");

        FileReader fr = new FileReader(selectedFile);
        BufferedReader br = new BufferedReader(fr);
        String line;
        while ((line = br.readLine()) != null) {
            if (!line.trim().equalsIgnoreCase("")) {
                if (line.trim().startsWith(INPUT)) {
                    if (inputSpec.toString().equals("")) {
                        inputSpec.append(line.trim().substring(INPUT.length()));
                    } else {
                        inputSpec.append(" , ").append(line.trim().substring(INPUT.length()));
                    }
                } else if (line.trim().startsWith(OUTPUT)) {
                    if (outputSpec.toString().equals("")) {
                        outputSpec.append(line.trim().substring(OUTPUT.length()));
                    } else {
                        outputSpec.append(" , ").append(line.trim().substring(OUTPUT.length()));
                    }
                } else if (line.trim().startsWith(TIMER)) {
                    if (timerSpec.toString().equals("")) {
                        timerSpec.append(line.trim().substring(OUTPUT.length()));
                    } else {
                        timerSpec.append(" , ").append(line.trim().substring(OUTPUT.length()));
                    }
                } else {
                    ltlSpec.append(line.trim()).append("\n");
                }
            }
        }
        br.close();

        map.put(INPUT, inputSpec.toString().trim());
        map.put(OUTPUT, outputSpec.toString().trim());
        map.put(TIMER, timerSpec.toString().trim());
        map.put(LTL, ltlSpec.toString());
        return map;

    }

    static ArrayList<String> getSignals(String signalText) {
        ArrayList<String> result = new ArrayList<String>();
        String[] signals = signalText.split(",");
        for (String signal : signals) {
            if (signal.trim().equals("") == false) {
                result.add(signal.trim());
            }
        }
        return result;
    }

    /**
     * Generate the LTL formula from the specification, where logical implications
     * are used to replace assumptions stated in the spec.
     * 
     * @param ltlSpec LTL specification under analysis
     * @return an LTL formula which can be understood by ltlbuchi or ltl2ba
     */
    static String parseLTLspecification(String ltlSpec) {
        String[] lines = ltlSpec.split("\\n");
        StringBuilder resultGuarantee = new StringBuilder("");
        StringBuilder resultAssume = new StringBuilder("");
        boolean firstLineGuarantee = true;
        boolean firstLineAssume = true;
        boolean hasAssume = false;
        for (String line : lines) {
            if (line.trim().startsWith("##") == false && line.trim().startsWith("!--") == false
                    && line.trim().equals("") == false) {
                if (line.trim().startsWith(ASSUME)) {
                    hasAssume = true;
                    // Cover the line to the spec
                    if (firstLineAssume) {
                        resultAssume.append("(").append(line.trim().substring(ASSUME.length())).append(")");
                        firstLineAssume = false;
                    } else {
                        resultAssume.append(" && (").append(line.trim().substring(ASSUME.length())).append(")");
                    }
                } else {
                    // Cover the line to the spec
                    if (firstLineGuarantee) {
                        resultGuarantee.append("(").append(line.trim()).append(")");
                        firstLineGuarantee = false;
                    } else {
                        resultGuarantee.append(" && (").append(line.trim()).append(")");
                    }
                }
            }
        }
        if (hasAssume) {
            return "(" + resultAssume.toString() + " ) -> (" + resultGuarantee.toString() + ")";
        } else {
            return resultGuarantee.toString();
        }
    }

    /**
     * Generate the LTL formula from the specification, where logical implications
     * are used to replace assumptions stated in the spec.
     * 
     * @param ltlSpec LTL specification under analysis
     * @return an LTL formula which can be understood by ltlbuchi or ltl2ba
     */
    static ArrayList<String> parseCompositionalLTLspecification(String ltlSpec) {

        String[] lines = ltlSpec.split("\\n");

        StringBuilder resultAssume = new StringBuilder("");
        ArrayList<StringBuilder> subGuaranteeList = new ArrayList<StringBuilder>();

        boolean firstLineAssume = true;
        boolean hasAssume = false;
        for (String line : lines) {
            if (line.trim().startsWith("##") == false && line.trim().startsWith("!--") == false
                    && line.trim().equals("") == false) {
                if (line.trim().startsWith(ASSUME)) {
                    hasAssume = true;
                    // Cover the line to the spec
                    if (firstLineAssume) {
                        resultAssume.append("(").append(line.trim().substring(ASSUME.length())).append(")");
                        firstLineAssume = false;
                    } else {
                        resultAssume.append(" && (").append(line.trim().substring(ASSUME.length())).append(")");
                    }
                }
            }
        }


        int currentAssembly = 0;
        StringBuilder guarantee = new StringBuilder("");

        for (String line : lines) {
            if (line.trim().startsWith("##") == false && line.trim().startsWith("!--") == false
                    && line.trim().equals("") == false) {
                if (!line.trim().startsWith(ASSUME)) {
                    // Cover the line to the spec
                    if (currentAssembly == 0) {
                        guarantee.append("(").append(line.trim()).append(")");
                    } else {
                        guarantee.append(" && (").append(line.trim()).append(")");
                    }
                    currentAssembly++;
                    if (currentAssembly == MAX_ASSEMBLY_GUARANTEES) {
                        subGuaranteeList.add(guarantee);
                        guarantee = new StringBuilder("");
                        currentAssembly = 0;
                    }
                }
            }
        }
        if (!guarantee.toString().equalsIgnoreCase("")) {
            // Add the remaining part back
            subGuaranteeList.add(guarantee);
        }


        ArrayList<String> result = new ArrayList<String>();
        if (hasAssume) {
            for (StringBuilder s : subGuaranteeList) {
                result.add("(" + resultAssume.toString() + " ) -> (" + s.toString() + ")");
            }
        } else {
            for (StringBuilder s : subGuaranteeList) {
                result.add(s.toString());
            }

        }
        return result;
    }

    /**
     * Perform LTL synthesis by reading a file.
     * 
     * @param selectedFile File to be parsed. 
     * @param optionTechnique Synthesis algorithm 
     * @param unrollSteps Unroll steps for Co-Buechi solver
     * @param outputFormat Desired output format 
     * @param isStrategyFinding Perform strategy finding (prove existence) or counter-strategy finding (prove non-existence)
     * @return Strategy or error message in textural form.
     * @throws Exception 
     */
    public ResultLTLSynthesis synthesizeFromFile(File selectedFile, int optionTechnique, int unrollSteps,
            int outputFormat, boolean isStrategyFinding) throws Exception {

        ResultLTLSynthesis result = new ResultLTLSynthesis();

        // outputMultiplexer = "";


        HashMap<String, String> map = getLTLSpecificationFromFile(selectedFile);

        ProblemDescription prob = new ProblemDescription(
                getSignals(map.get(INPUT)),
                getSignals(map.get(OUTPUT)),
                 getSignals(map.get(TIMER)),
                SolverUtility.parseLTLspecification(changeSpecToInternalFormat(map.get(LTL))),
                unrollSteps);



        boolean isNumericalLTLAnalysis = false;
        if (!Version.BSD_VERSION) {
            if (!GraphicsEnvironment.isHeadless()) {
                // gui mode
                int n = JOptionPane.showConfirmDialog(
                        null,
                        "Perform numerical LTL synthesis?",
                        "G4LTL",
                        JOptionPane.YES_NO_OPTION);
                if (n == JOptionPane.OK_OPTION) {
                    isNumericalLTLAnalysis = true;
                }
            }
        }



        if (!Version.BSD_VERSION) {
            // Check if optimization can be applied.
            ArrayList<String> spec = new ArrayList<String>();
            String[] ss = map.get(LTL).split("\\n");
            for (String s : ss) {
                if (!s.trim().equals("")) {
                    spec.add(s);
                }
            }

            CompressibilityCheck check = new CompressibilityCheck();

            if (outputFormat == SynthesisEngine.OUTPUT_FSM_ACTOR_PTOLEMY) {
                check.checkCompressibility(spec, prob);

                if (check.isCompressible()) {
                    if (check.getNewOutputVariables().isEmpty()) {
                        result.setStrategyFound(false);
                        result.setMessage1("Not realizable due to impossibility of generating outputs");
                        return result;
                    } else {
                        // Set new output variables
                        prob.setOutputVariables(check.getNewOutputVariables());
                        // Set new specification
                        prob.setLtlSpecification(SolverUtility.parseLTLspecification(
                                SolverUtility.changeSpecToInternalFormat(check.getRewrittenSpecification())));
                    }
                }
            }


            // Invoke the engine, and redirect the synthesized result to the result panel.
            SynthesisEngine engine = new SynthesisEngine();

            if (optionTechnique == SynthesisEngine.COBUECHI_SOLVER) {
                result = engine.invokeMonolithicCoBuechiEngine(prob, false, outputFormat, isStrategyFinding);
            } else {
                result = engine.invokeMonolithicBuechiEngine(prob, false, outputFormat, isStrategyFinding);
            }

            if (outputFormat == SynthesisEngine.OUTPUT_FSM_ACTOR_PTOLEMY) {
                if (result.isStrategyFound()) {

                    if (check.isCompressible()) {
                        // Prepare the output multiplexer
                        result.setMessage2(PtolemyTemplate.createPtolemyMultiplexerCode(check.getNewOutputVariables(),
                                check.getRewrittenOutputVariables(),
                                check.getOutputCombinationList()) + "\n");

                    }
                }
            }
        } else {

            // Invoke the engine, and redirect the synthesized result to the result panel.
            SynthesisEngine engine = new SynthesisEngine();

            if (optionTechnique == SynthesisEngine.COBUECHI_SOLVER) {
                result = engine.invokeMonolithicCoBuechiEngine(prob, false, outputFormat, isStrategyFinding);
            } else {
                result = engine.invokeMonolithicBuechiEngine(prob, false, outputFormat, isStrategyFinding);
            }
        }


        return result;
    }

    public static String getPolynomialSpecificationFromFile(File selectedFile) {

        StringBuilder polynomialSpec = new StringBuilder("");
        try {
            FileReader fr = new FileReader(selectedFile);
            BufferedReader br = new BufferedReader(fr);
            String line;
            while ((line = br.readLine()) != null) {
                polynomialSpec.append(line.trim()).append("\n");
            }
            br.close();
        } catch (Exception ex) {
            System.out.println(ex.toString());
        }
        return polynomialSpec.toString();

    }
}

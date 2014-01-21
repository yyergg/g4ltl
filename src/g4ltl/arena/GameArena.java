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
package g4ltl.arena;

import java.io.*;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

/**
 * 
 * @author Chihhong Cheng
 * @version 0.2 2012/08/08
 */
public class GameArena  {

    public ArrayList<VertexEdgeSet> vertexList = new ArrayList<VertexEdgeSet>();
    private String name;

        /** Creates a new instance of BuchiAutomaton */
    public GameArena() {
        vertexList = new ArrayList<VertexEdgeSet>();
    }

    
    /** Retrieve the name of the automaton. */
    public String getName() {
        return this.name;
    }

    /** Set the automaton with the name passed by the parameter. */
    public void setName(String paraName) {
        this.name = paraName;
    }


    /**
     * Override the equal function for comparison of two automata.
     *
     * @return True if two automata are equal under deep comparison. False if
     *         two automata are not equal.
     */
    public boolean equals(Object objectAutomaton) {
        GameArena automaton = (GameArena) objectAutomaton;
        if (vertexList.equals(automaton.vertexList)) {
            return true;
        } else {
            return false;
        }
    }



    public ArrayList<HashSet<Integer>> getSpecificationDescription(
            File selectedFile, HashMap<String, String> name_id_Map) {
        ArrayList<HashSet<Integer>> returnList = new ArrayList<HashSet<Integer>>();

        try {
            FileReader fr = new FileReader(selectedFile);
            BufferedReader br = new BufferedReader(fr);
            String line = null;


            while ((line = br.readLine()) != null) {
                if (!line.trim().equalsIgnoreCase("")) {
                    HashSet<Integer> set = new HashSet<Integer>();
                    String[] lineInBr = line.split(" ");
                    for (int i = 0; i
                            < lineInBr.length; i++) {
                        if (lineInBr[i].trim().equalsIgnoreCase("") == false) {
                            set.add(new Integer(name_id_Map.get(lineInBr[i])));
                        }
                    }
                    returnList.add(set);
                }
            }
            br.close();

        } catch (FileNotFoundException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (Exception e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        return returnList;

    }

}

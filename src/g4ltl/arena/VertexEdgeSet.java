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


import java.util.ArrayList;


@SuppressWarnings("serial")
/**
 * We explicitly assume that each vertex, during the construction, has different ID.
 * 
 * @author Chihhong Cheng
 * @version 0.2 2012/08/08
 */
public class VertexEdgeSet  {

    public final static int COLOR_NONFINAL = 0;
    public final static int COLOR_FINAL = 1;
    /**
     * This constant is used to indicated that the vertex is initial and
     * control.
     */
    public final static int INITIAL_CONTROL = 1;
    /**
     * This constant is used to indicated that the vertex is initial and plant.
     */
    public final static int INITIAL_PLANT = 2;
    /**
     * This constant is used to indicated that the vertex is not initial but
     * control.
     */
    public final static int NONINITIAL_CONTROL = 3;
    /**
     * This constant is used to indicated that the vertex is neither initial nor
     * control.
     */
    public final static int NONINITIAL_PLANT = 4;
    // vertexStatus is used as the coloring function when the automaton is interpreted as the game arena.
    public int vertexStatus;
    public ArrayList<EdgeElement> edgeSet = new ArrayList<EdgeElement>();
    protected int vertexProperty;
    protected int vertexID;
    protected int vertexColor;

    public VertexEdgeSet() {
        // TODO Auto-generated constructor stub
    }

    public int getVertexColor() {
        return this.vertexColor;
    }

    public void setVertexColor(int paraVertexColor) {
        this.vertexColor = paraVertexColor;
    }

    public int getVertexID() {
        return this.vertexID;
    }

    public void setVertexID(int paraVertexID) {
        this.vertexID = paraVertexID;
    }

    public int getVertexProperty() {
        return this.vertexProperty;
    }

    public void setVertexProperty(int paraVertexProperty) {
        this.vertexProperty = paraVertexProperty;
    }

    public boolean equals(Object o) {
        if (this.vertexID == ((VertexEdgeSet) o).vertexID) {
            return true;
        } else {
            return false;
        }
    }

    public int hashCode() {
        return this.vertexID;
    }
}

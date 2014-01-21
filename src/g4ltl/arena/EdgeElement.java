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


import java.util.HashSet;

/**
 * 
 * @author Chihhong Cheng
 * @version 0.2 2012/08/08
 */
public class EdgeElement  {


    public EdgeElement(int sourceVertexID, int destVertexID, String edgeLabel, int edgeStatus) {
        this.sourceVertexID = sourceVertexID;
        this.destVertexID = destVertexID;
        this.edgeLabel.add(edgeLabel);
        this.edgeStatus = edgeStatus;
    }
    protected int sourceVertexID;
    protected int destVertexID;
    HashSet<String> edgeLabel = new HashSet<String>();
    protected int edgeStatus;

    public int getDestVertexID() {
        return this.destVertexID;
    }

    public void setDestVertexID(int paraVertexID) {
        this.destVertexID = paraVertexID;
    }

    public int getSourceVertexID() {
        return this.sourceVertexID;
    }

    public void setSourceVertexID(int paraVertexID) {
        this.sourceVertexID = paraVertexID;
    }

    public HashSet<String> getEdgeLabel() {
        return this.edgeLabel;
    }   

    public int getEdgeStatus() {
        return this.edgeStatus;
    }

    public void setEdgeStatus(int paraEdgeStatus) {
        this.edgeStatus = paraEdgeStatus;
    }

    /**
     * Creates a new instance of EdgeElement
     */
    public EdgeElement() {
    }

    public boolean equals(Object o) {
        EdgeElement e = (EdgeElement) o;
        if ((sourceVertexID == e.sourceVertexID) && (destVertexID == e.destVertexID) && (edgeLabel.equals(e.edgeLabel))) {
            return true;
        } else {
            return false;
        }
    }
}

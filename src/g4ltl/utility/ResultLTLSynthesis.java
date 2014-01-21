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

import java.util.HashSet;

/**
 * Container for describing the result of LTL synthesis.
 * 
 * @author Chihhong Cheng
 * @version 0.3 2013/02/28
 */
public class ResultLTLSynthesis {

    private boolean strategyFound;
    private String message1 = "";
    private String message2 = "";
    private HashSet<String> tokenSet;

    public boolean isStrategyFound() {
        return this.strategyFound;
    }

    public String getMessage1() {
        return this.message1;
    }

    public String getMessage2() {
        return this.message2;
    }

    public HashSet<String> getTokenSet() {
        return this.tokenSet;
    }

    public void setStrategyFound(boolean s) {
        this.strategyFound = s;
    }

    public void setMessage1(String msg) {
        this.message1 = msg;
    }

    public void setMessage2(String msg) {
        this.message2 = msg;
    }

    public void setTokenSet(HashSet<String> set) {
        this.tokenSet = set;
    }
}

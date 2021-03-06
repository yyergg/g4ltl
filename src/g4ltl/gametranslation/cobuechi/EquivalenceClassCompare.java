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

import java.io.Serializable;
import java.util.Arrays;
import java.util.Comparator;

/**
 * EquivalenceClass.java Purpose: Compare whether two equivalence classes are
 * the same.
 *
 * @author Chihhong Cheng
 * @version 0.2 2012/08/08
 */
public class EquivalenceClassCompare implements Serializable, Comparator<EquivalenceClass> {

    public EquivalenceClassCompare() {
    }

    public int compare(EquivalenceClass one, EquivalenceClass two) {
        if (one.isEnv == two.isEnv
                && one.inputVector.equals(two.inputVector)
                && one.accumulator.equals(two.accumulator)
                && one.controlVertex.equals(two.controlVertex)
                //&& Arrays.equals(one.accumulator, two.accumulator)
                // && Arrays.equals(one.controlVertex, two.controlVertex)
            ) {
            for (int i = 0; i < one.score.length; i++) {
                if (!Arrays.equals(one.score[i], two.score[i])) {
                    return -1;
                }
            }
            return 0;
        } else {
            return -1;
        }
    }
}

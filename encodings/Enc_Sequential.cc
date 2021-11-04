/*!
 * \author Ruben Martins - rubenm@andrew.cmu.edu
 *
 * @section LICENSE
 *
 * VeriPBLib, Copyright (c) 2021, Ruben Martins
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 */

#include "Enc_Sequential.h"

using namespace openwbo;

void Sequential::encode(Card *card, MaxSATFormula *maxsat_formula){


// s_{1,1} -y1 0
// y1 -s_{1,1} 0
// s_{2,1} -y2 0
// s_{2,1} -s_{1,1} 0
// s_{1,1} y2 -s_{2,1} 0
// s_{2,2} -s_{1,1} -y2 0
// y2 -s_{2,2} 0
// s_{1,1} -s_{2,2} 0
// s_{3,1} -y3 0
// s_{3,1} -s_{2,1} 0
// s_{2,1} y3 -s_{3,1} 0
// s_{3,2} -s_{2,1} -y3 0
// s_{3,2} -s_{2,2} 0
// s_{2,2} y3 -s_{3,2} 0
// s_{2,2} s_{2,1} -s_{3,2} 0
// s_{3,1} 0
// -s_{3,2} 0

  // Create auxiliary variables.
  int n = card->_lits.size();
  vec<Lit> *seq_auxiliary = new vec<Lit>[n + 1];
  for (int i = 0; i < n + 1; i++)
    seq_auxiliary[i].growTo(card->_rhs + 1);

  for (int i = 1; i <= n; ++i) {
    for (int j = 1; j <= (int)(card->_rhs); ++j) {
      seq_auxiliary[i][j] = mkLit(maxsat_formula->nVars(), false);
      maxsat_formula->newVar();
    }
  }

//   for (int i = 1; i <= (int)rhs; ++i)
//     pb_outlits.push(seq_auxiliary[n][i]);

  for (int i = 1; i <= n; i++) {
    int wi = 1; // this could be generalized to the weighted case

    for (int j = 1; j <= (int)(card->_rhs); j++) {
      if (i >= 2 && i <= n && j <= (int)(card->_rhs)) {
        addBinaryClause(maxsat_formula, ~seq_auxiliary[i - 1][j], seq_auxiliary[i][j]);
      }
      if (i <= n && j <= wi) {
        addBinaryClause(maxsat_formula, ~card->_lits[i - 1], seq_auxiliary[i][j]);
      }
      if (i >= 2 && i <= n && j <= (int)(card->_rhs - wi)) {
        addTernaryClause(maxsat_formula, ~seq_auxiliary[i - 1][j], ~card->_lits[i - 1],
                         seq_auxiliary[i][j + wi]);
      }
    }

    // Encode rhs.
    if (i >= 2) {
      addBinaryClause(maxsat_formula, ~seq_auxiliary[i - 1][(int)(card->_rhs) + 1 - (int)wi],
                      ~card->_lits[i - 1]);
    }
  }

  if (card->_sign == _PB_EQUAL_){

  }

}

/*!
 * \author Ruben Martins - rubenm@andrew.cmu.edu
 *
 * @section LICENSE
 *
 * VeritasPBLib, Copyright (c) 2021, Ruben Martins
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

#include "USequential.h"

using namespace openwbo;

void USequential::encode(Card *card, MaxSATFormula *maxsat_formula, pb_Sign sign){
  assert (sign != _PB_EQUAL_);

  vec<Lit> lits;
  vec<Lit> pb_outlits;
  vec<uint64_t> coeffs;
  
  card->_lits.copyTo(lits);

  // code adapted from Open-WBO
  // would also support PB constraints using the sequential encoding
  coeffs.growTo(lits.size(), 1);

  uint64_t rhs = card->_rhs;
  int n = lits.size();

  // transform it into <=
  if (sign == _PB_GREATER_OR_EQUAL_){
    int s = 0;
      for (int i = 0; i < coeffs.size(); i++) {
        s += coeffs[i];
        lits[i] = ~(lits[i]);
      }
      rhs = s - rhs;
  }

  // simplifications
  // all literals must be assigned to 0
  if (rhs == 0){
    for (int i = 0; i < lits.size(); i++){
      addUnitClause(maxsat_formula, ~lits[i]);
    }
    return;
  }


  // <= encoding needs to count rhs+1
  rhs = rhs +1;

  // Create auxiliary variables.
  vec<Lit> *seq_auxiliary = new vec<Lit>[n + 1];
  for (int i = 0; i < n + 1; i++)
    seq_auxiliary[i].growTo(rhs + 1);

  for (int i = 1; i <= n; ++i) {
    for (int j = 1; j <= (int)rhs; ++j) {
      seq_auxiliary[i][j] = mkLit(maxsat_formula->nVars(), false);
      maxsat_formula->newVar();
    }
  }

  for (int i = 1; i <= n; i++) {
    // WARNING: wi is used as int for array indexes but as int64_t
    // for the coeffs. Dangerous if the coeffs are larger than INT32_MAX.
    // Same problem occurs with rhs.
    uint64_t wi = coeffs[i - 1];
    // assert(wi <= rhs);

    for (int j = 1; j <= (int)rhs; j++) {
      if (i >= 2 && i <= n && j <= (int)rhs) {
        addBinaryClause(maxsat_formula, ~seq_auxiliary[i - 1][j], seq_auxiliary[i][j]);
      }
      if (i <= n && j <= (int)wi) {
        addBinaryClause(maxsat_formula, ~lits[i - 1], seq_auxiliary[i][j]);
      }
      if (i >= 2 && i <= n && j <= (int)(rhs - wi)) {
        addTernaryClause(maxsat_formula, ~seq_auxiliary[i - 1][j], ~lits[i - 1],
                         seq_auxiliary[i][j + (int)wi]);
      }
    }

    if (i >= 2) {
      addBinaryClause(maxsat_formula, ~seq_auxiliary[i - 1][(int)rhs + 1 - (int)wi],
                      ~lits[i - 1]);
    }
  }

  // Set the maximum sum to be smaller than rhs
  addUnitClause(maxsat_formula, ~seq_auxiliary[n][rhs]);

}

void USequential::encode(Card *card, MaxSATFormula *maxsat_formula){

    switch (card->_sign){
      case _PB_EQUAL_:
        encode(card, maxsat_formula, _PB_GREATER_OR_EQUAL_);
        encode(card, maxsat_formula, _PB_LESS_OR_EQUAL_);
        break;
      case _PB_LESS_OR_EQUAL_:
        encode(card, maxsat_formula, _PB_LESS_OR_EQUAL_);
        break;
      case _PB_GREATER_OR_EQUAL_:
        encode(card, maxsat_formula, _PB_GREATER_OR_EQUAL_);
        break;
      default:
        assert(false);
    }

}

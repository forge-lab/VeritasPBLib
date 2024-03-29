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

void USequential::encode(Card *card, MaxSATFormula *maxsat_formula,
                         pb_Sign sign) {
  vec<Lit> lits;
  uint64_t rhs = card->_rhs;
  card->_lits.copyTo(lits);
  int n = lits.size();

  // >= we need to fix output @rhs with positive literal
  // <= we need to fix output @(rhs+1) with negative literal

  pb_Sign current_sign = sign;

  // simplifications
  // all literals must be assigned to 0
  if (rhs == 0 && current_sign == _PB_LESS_OR_EQUAL_) {
    for (int i = 0; i < lits.size(); i++) {
      addUnitClause(maxsat_formula, card, ~lits[i]);
    }
    return;
  }
  // all literals must be assigned to 1
  if (rhs == n && current_sign == _PB_GREATER_OR_EQUAL_) {
    for (int i = 0; i < lits.size(); i++) {
      addUnitClause(maxsat_formula, card, lits[i]);
    }
    return;
  }
  // constraint is no restriction
  if (rhs == n && current_sign == _PB_LESS_OR_EQUAL_) {
    return;
  }
  if (rhs == 0 && current_sign == _PB_GREATER_OR_EQUAL_) {
    return;
  }

  // transform the constraint to consider the smallest rhs
  if (n - rhs < rhs) {
    int s = 0;
    for (int i = 0; i < lits.size(); i++) {
      s += 1;
      lits[i] = ~(lits[i]);
    }
    rhs = s - rhs;
    if (current_sign != _PB_EQUAL_) {
      if (current_sign == _PB_GREATER_OR_EQUAL_)
        current_sign = _PB_LESS_OR_EQUAL_;
      else
        current_sign = _PB_GREATER_OR_EQUAL_;
    }
  }

  uint64_t k = rhs;
  k++; // for proof logging we always treat it as a _PB_LESS_OR_EQUAL_ ctr

  // TODO: creating some variables that may not be used in the encoding
  // Example: if >= we are creating k+1 for the pbp format ;
  // TODO: only create these variables for the pbp format

  // Create auxiliary variables.
  vec<Lit> *seq_auxiliary = new vec<Lit>[n];
  for (int i = 0; i < n; i++) {
    if (i + 1 <= k)
      seq_auxiliary[i].growTo(i + 1);
    else
      seq_auxiliary[i].growTo(k + 1);
    for (int j = 0; j < seq_auxiliary[i].size(); j++) {
      seq_auxiliary[i][j] = mkLit(maxsat_formula->nVars(), false);
      maxsat_formula->newVar();
    }
  }

  if (current_sign == _PB_GREATER_OR_EQUAL_)
    k--;

  addBinaryClause(maxsat_formula, card, ~lits[0], seq_auxiliary[0][0]);
  addBinaryClause(maxsat_formula, card, lits[0], ~seq_auxiliary[0][0]);

  for (int i = 1; i < n; i++) {
    addBinaryClause(maxsat_formula, card, ~lits[i], seq_auxiliary[i][0]);

    if (i + 1 == seq_auxiliary[i].size()) {
      addBinaryClause(maxsat_formula, card, lits[i], ~seq_auxiliary[i][i]);
    }

    for (int j = 0; j <= k; j++) {
      if (j < seq_auxiliary[i - 1].size())
        addTernaryClause(maxsat_formula, card, lits[i], seq_auxiliary[i - 1][j],
                         ~seq_auxiliary[i][j]);

      if (j < seq_auxiliary[i - 1].size())
        addBinaryClause(maxsat_formula, card, ~seq_auxiliary[i - 1][j],
                        seq_auxiliary[i][j]);

      if (j > 0 && j < seq_auxiliary[i].size())
        addTernaryClause(maxsat_formula, card, ~lits[i],
                         ~seq_auxiliary[i - 1][j - 1], seq_auxiliary[i][j]);

      if (j > 0 && j < seq_auxiliary[i].size()) {
        addBinaryClause(maxsat_formula, card, seq_auxiliary[i - 1][j - 1],
                        ~seq_auxiliary[i][j]);
      }
    }
  }

  if (current_sign == _PB_GREATER_OR_EQUAL_ || current_sign == _PB_EQUAL_) {
    addUnitClause(maxsat_formula, card, seq_auxiliary[n - 1][rhs - 1]);
  }
  if (current_sign == _PB_LESS_OR_EQUAL_ || current_sign == _PB_EQUAL_) {
    addUnitClause(maxsat_formula, card, ~seq_auxiliary[n - 1][rhs]);
  }
}

void USequential::encode(Card *card, MaxSATFormula *maxsat_formula) {

  switch (card->_sign) {
  case _PB_EQUAL_:
    encode(card, maxsat_formula, _PB_EQUAL_);
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

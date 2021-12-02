/*!
 * \author Ruben Martins - rubenm@andrew.cmu.edu
 *
 * @section LICENSE
 *
 * VeritasPBLib, Copyright (c) 2021, Ruben Martins, Stephan Gocht, Jakob Nordstrom
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

#include "UTotalizer.h"

using namespace openwbo;

void UTotalizer::adder(MaxSATFormula *maxsat_formula, vec<Lit> &left, vec<Lit> &right,
                      vec<Lit> &output) {
  assert(output.size() == left.size() + right.size());
  // We only need to count the sums up to k.
  for (int i = 0; i <= left.size(); i++) {
    for (int j = 0; j <= right.size(); j++) {
      if (i == 0 && j == 0)
        continue;

      if (i + j > _rhs+1)
        continue;

      if (i == 0) {
        addBinaryClause(maxsat_formula, ~right[j - 1], output[j - 1]);
      } else if (j == 0) {
        addBinaryClause(maxsat_formula, ~left[i - 1], output[i - 1]);
      } else {
        addTernaryClause(maxsat_formula, ~left[i - 1], ~right[j - 1], output[i + j - 1]);
      }
    }
  }
}

void UTotalizer::toCNF(MaxSATFormula *maxsat_formula, vec<Lit> &lits){
  vec<Lit> left;
  vec<Lit> right;

  assert(lits.size() > 1);
  int split = floor(lits.size() / 2);

  for (int i = 0; i < lits.size(); i++) {

    if (i < split) {
      // left branch
      if (split == 1) {
        assert(cardinality_inlits.size() > 0);
        left.push(cardinality_inlits.last());
        cardinality_inlits.pop();
      } else {
        Lit p = mkLit(maxsat_formula->nVars(), false);
        maxsat_formula->newVar();
        left.push(p);
      }
    } else {

      // right branch
      if (lits.size() - split == 1) {
        assert(cardinality_inlits.size() > 0);
        right.push(cardinality_inlits.last());
        cardinality_inlits.pop();
      } else {
        Lit p = mkLit(maxsat_formula->nVars(), false);
        maxsat_formula->newVar();
        right.push(p);
      }
    }
  }

  if (left.size() > 1)
    toCNF(maxsat_formula, left);
  if (right.size() > 1)
    toCNF(maxsat_formula, right);
  adder(maxsat_formula, left, right, lits);
}

void UTotalizer::encode(Card *card, MaxSATFormula *maxsat_formula, pb_Sign sign){
  assert (sign != _PB_EQUAL_);

  vec<Lit> lits;
  vec<Lit> pb_outlits;
  vec<int64_t> coeffs;
  
  card->_lits.copyTo(lits);

  // code adapted from Open-WBO
  // would also support PB constraints using the sequential encoding
  coeffs.growTo(lits.size(), 1);

  _rhs = card->_rhs;
  
  // transform it into <=
  if (sign == _PB_GREATER_OR_EQUAL_){
    int s = 0;
      for (int i = 0; i < coeffs.size(); i++) {
        s += coeffs[i];
        lits[i] = ~(lits[i]);
      }
      _rhs = s - _rhs;
  }
  
  // simplifications
  // all literals must be assigned to 0
  if (_rhs == 0){
    for (int i = 0; i < lits.size(); i++){
      addUnitClause(maxsat_formula, ~lits[i]);
    }
    return;
  }

  for (int i = 0; i < lits.size(); i++) {
    Lit p = mkLit(maxsat_formula->nVars(), false);
    maxsat_formula->newVar();
    cardinality_outlits.push(p);
  }

  lits.copyTo(cardinality_inlits);

  toCNF(maxsat_formula, cardinality_outlits);
  assert(cardinality_inlits.size() == 0);

  for (int i = _rhs; i < cardinality_outlits.size(); i++)
      addUnitClause(maxsat_formula, ~cardinality_outlits[i]);

}

void UTotalizer::encode(Card *card, MaxSATFormula *maxsat_formula){

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
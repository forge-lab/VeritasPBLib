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

#include "VSequential.h"
#include <iostream>

using namespace openwbo;

void VSequential::encode(Card *card, MaxSATFormula *maxsat_formula, pb_Sign sign){
  assert (sign != _PB_EQUAL_);


//   * #variable= 4 #constraint= 1
// 1 y1 1 y2 1 y3 1 y4 >= 2 ;
// p cnf 11 23
// -y1 s_{1,1} 0
// y1 -s_{1,1} 0
// -y2 s_{2,1} 0
// -s_{1,1} s_{2,1} 0
// y2 s_{1,1} -s_{2,1} 0
// -y2 -s_{1,1} s_{2,2} 0
// y2 -s_{2,2} 0
// s_{1,1} -s_{2,2} 0
// -y3 s_{3,1} 0
// -s_{2,1} s_{3,1} 0
// y3 s_{2,1} -s_{3,1} 0
// -y3 -s_{2,1} s_{3,2} 0
// -s_{2,2} s_{3,2} 0
// y3 s_{2,2} -s_{3,2} 0
// s_{2,1} s_{2,2} -s_{3,2} 0
// -y4 s_{4,1} 0
// -s_{3,1} s_{4,1} 0
// y4 s_{3,1} -s_{4,1} 0
// -y4 -s_{3,1} s_{4,2} 0
// -s_{3,2} s_{4,2} 0
// y4 s_{3,2} -s_{4,2} 0
// s_{3,1} s_{3,2} -s_{4,2} 0
// s_{4,2} 0


// pseudo-Boolean proof version 1.2
// f 1 0
// # 1
// red 1 y1 1 ~s_{1,1} >= 1 ; s_{1,1} -> 0
// red 1 ~y1 1 s_{1,1} >= 1 ; s_{1,1} -> 1
// red 1 s_{1,1} 1 y2 1 ~s_{2,1} >= 1 ; s_{2,1} -> 0
// red 1 ~s_{1,1} 1 ~y2 2 s_{2,1} >= 2 ; s_{2,1} -> 1
// red 1 s_{1,1} 1 y2 2 ~s_{2,2} >= 2 ; s_{2,2} -> 0
// red 1 ~s_{1,1} 1 ~y2 1 s_{2,2} >= 1 ; s_{2,2} -> 1
// p 5 6 + 2 d
// e -1 1 s_{2,1} 1 ~s_{2,2} >= 1 ;
// red 1 s_{2,1} 1 s_{2,2} 1 y3 1 ~s_{3,1} >= 1 ; s_{3,1} -> 0
// red 1 ~s_{2,1} 1 ~s_{2,2} 1 ~y3 3 s_{3,1} >= 3 ; s_{3,1} -> 1
// red 1 s_{2,1} 1 s_{2,2} 1 y3 2 ~s_{3,2} >= 2 ; s_{3,2} -> 0
// red 1 ~s_{2,1} 1 ~s_{2,2} 1 ~y3 2 s_{3,2} >= 2 ; s_{3,2} -> 1
// p 10 11 + 3 d
// e -1 1 s_{3,1} 1 ~s_{3,2} >= 1 ;
// red 1 s_{2,1} 1 s_{2,2} 1 y3 3 ~s_{3,3} >= 3 ; s_{3,3} -> 0
// red 1 ~s_{2,1} 1 ~s_{2,2} 1 ~y3 1 s_{3,3} >= 1 ; s_{3,3} -> 1
// p 12 14 + 3 d
// e -1 1 s_{3,2} 1 ~s_{3,3} >= 1 ;
// red 1 s_{3,1} 1 s_{3,2} 1 y4 1 ~s_{4,1} >= 1 ; s_{4,1} -> 0
// red 1 ~s_{3,1} 1 ~s_{3,2} 1 ~y4 3 s_{4,1} >= 3 ; s_{4,1} -> 1
// red 1 s_{3,1} 1 s_{3,2} 1 y4 2 ~s_{4,2} >= 2 ; s_{4,2} -> 0
// red 1 ~s_{3,1} 1 ~s_{3,2} 1 ~y4 2 s_{4,2} >= 2 ; s_{4,2} -> 1
// p 18 19 + 3 d
// e -1 1 s_{4,1} 1 ~s_{4,2} >= 1 ;
// red 1 s_{3,1} 1 s_{3,2} 1 y4 3 ~s_{4,3} >= 3 ; s_{4,3} -> 0
// red 1 ~s_{3,1} 1 ~s_{3,2} 1 ~y4 1 s_{4,3} >= 1 ; s_{4,3} -> 1
// p 20 22 + 3 d
// e -1 1 s_{4,2} 1 ~s_{4,3} >= 1 ;
// p 2 4 6 + 2 d + 9 11 + 2 d 2 * 14 + 3 d + 17 19 + 2 d 2 * 22 + 3 d +
// p 3 7 5 + 2 d + 15 12 + 2 d 2 * 10 + 3 d + 23 20 + 2 d 2 * 18 + 3 d +
// p 26 1 +
// # 0
// u 1 ~y1 1 s_{1,1} >= 1 ;
// u 1 s_{1,1} >= 0 ;
// u 1 y1 1 ~s_{1,1} >= 1 ;
// u 1 ~s_{1,1} >= 0 ;
// u 1 ~y2 1 s_{2,1} >= 1 ;
// u 1 ~s_{1,1} 1 s_{2,1} >= 1 ;
// u 1 y2 1 s_{1,1} 1 ~s_{2,1} >= 1 ;
// u 1 s_{1,1} 1 ~s_{2,1} >= 0 ;
// u 1 ~y2 1 ~s_{1,1} 1 s_{2,2} >= 1 ;
// u 1 s_{2,2} >= 0 ;
// u 1 y2 1 ~s_{2,2} >= 1 ;
// u 1 s_{1,1} 1 ~s_{2,2} >= 1 ;
// u 1 ~y3 1 s_{3,1} >= 1 ;
// u 1 ~s_{2,1} 1 s_{3,1} >= 1 ;
// u 1 y3 1 s_{2,1} 1 ~s_{3,1} >= 1 ;
// u 1 s_{2,1} 1 ~s_{3,1} >= 0 ;
// u 1 ~y3 1 ~s_{2,1} 1 s_{3,2} >= 1 ;
// u 1 ~s_{2,2} 1 s_{3,2} >= 1 ;
// u 1 y3 1 s_{2,2} 1 ~s_{3,2} >= 1 ;
// u 1 s_{2,1} 1 s_{2,2} 1 ~s_{3,2} >= 1 ;
// u 1 ~y4 1 s_{4,1} >= 1 ;
// u 1 ~s_{3,1} 1 s_{4,1} >= 1 ;
// u 1 y4 1 s_{3,1} 1 ~s_{4,1} >= 1 ;
// u 1 s_{3,1} 1 ~s_{4,1} >= 0 ;
// u 1 ~y4 1 ~s_{3,1} 1 s_{4,2} >= 1 ;
// u 1 ~s_{3,2} 1 s_{4,2} >= 1 ;
// u 1 y4 1 s_{3,2} 1 ~s_{4,2} >= 1 ;
// u 1 s_{3,1} 1 s_{3,2} 1 ~s_{4,2} >= 1 ;
// u 1 s_{4,2} >= 1 ;
// w 1

vec<Lit> lits;
uint64_t rhs = card->_rhs;
card->_lits.copyTo(lits);
int n = lits.size();

// >= we need to fix output @rhs with positive literal
// <= we need to fix output @(rhs+1) with negative literal

pb_Sign current_sign = sign;

// transform the constraint to consider the smallest rhs
if (n-rhs < rhs){
  int s = 0;
      for (int i = 0; i < lits.size(); i++) {
        s += 1;
        lits[i] = ~(lits[i]);
      }
      rhs = s - rhs;
      if (current_sign == _PB_GREATER_OR_EQUAL_) current_sign = _PB_LESS_OR_EQUAL_;
      else current_sign = _PB_GREATER_OR_EQUAL_;
}

uint64_t k = rhs;
if (current_sign == _PB_LESS_OR_EQUAL_) k++;

// TODO: simplify the cardinality constraint? 
// <= 0 -> all literals are negative; >= n -> all literals are positive  

// Create auxiliary variables.
vec<Lit> *seq_auxiliary = new vec<Lit>[n];
  for (int i = 0; i < n; i++){
    if (i+1 < k) seq_auxiliary[i].growTo(i+1);
    else seq_auxiliary[i].growTo(k);
    for (int j = 0; j < seq_auxiliary[i].size(); j++){
      seq_auxiliary[i][j] = mkLit(maxsat_formula->nVars(), false);
      maxsat_formula->newVar();
    }
  }

  std::cout << "k=" << k << std::endl;
  std::cout << "n=" << n << std::endl;

  // -y1 s_{1,1} 0
  // y1 -s_{1,1} 0
  addBinaryClause(maxsat_formula, ~lits[0], seq_auxiliary[0][0]);
  addBinaryClause(maxsat_formula, lits[0], ~seq_auxiliary[0][0]);

  for (int i = 1; i < n; i++){
    // -y2 s_{2,1} 0
    // -y3 s_{3,1} 0
    // -y4 s_{4,1} 0    
    addBinaryClause(maxsat_formula, ~lits[i], seq_auxiliary[i][0]);

    if (i+1 == seq_auxiliary[i].size()){
      // y2 -s_{2,2} 0
      addBinaryClause(maxsat_formula, lits[i], ~seq_auxiliary[i][i]);
      // s_{1,1} -s_{2,2} 0
      addBinaryClause(maxsat_formula, seq_auxiliary[i-1][i-1], ~seq_auxiliary[i][i]);
    }

    for (int j = 0; j < k; j++){
      // y2 s_{1,1} -s_{2,1} 0
      // y3 s_{2,1} -s_{3,1} 0
      // y3 s_{2,2} -s_{3,2} 0
      // y4 s_{3,1} -s_{4,1} 0
      // y4 s_{3,2} -s_{4,2} 0
      if (j < seq_auxiliary[i-1].size()) addTernaryClause(maxsat_formula, lits[i], seq_auxiliary[i-1][j],~seq_auxiliary[i][j]);

      // -s_{1,1} s_{2,1} 0
      // -s_{2,1} s_{3,1} 0
      // -s_{2,2} s_{3,2} 0
      // -s_{3,2} s_{4,2} 0
      // -s_{3,1} s_{4,1} 0 
      if (j < seq_auxiliary[i-1].size()) addBinaryClause(maxsat_formula, ~seq_auxiliary[i-1][j], seq_auxiliary[i][j]);

      if (j+1 < k && j < seq_auxiliary[i-1].size()) addTernaryClause(maxsat_formula, ~lits[i], ~seq_auxiliary[i-1][j], seq_auxiliary[i][j+1]);
      // -y2 -s_{1,1} s_{2,2} 0
      // -y3 -s_{2,1} s_{3,2} 0
      // -y4 -s_{3,1} s_{4,2} 0

      if (i > 1 && j+1 < k && j < seq_auxiliary[i-1].size() && j+1 < seq_auxiliary[i-1].size()){
        addTernaryClause(maxsat_formula, seq_auxiliary[i-1][j], seq_auxiliary[i-1][j+1], ~seq_auxiliary[i][j+1]);
      } 
      // s_{2,1} s_{2,2} -s_{3,2} 0      
      // s_{3,1} s_{3,2} -s_{4,2} 0
    }
  }

// s_{4,2} 0
if (current_sign == _PB_GREATER_OR_EQUAL_) addUnitClause(maxsat_formula, seq_auxiliary[n-1][k-1]);
else addUnitClause(maxsat_formula, ~seq_auxiliary[n-1][k-1]);


}

void VSequential::encode(Card *card, MaxSATFormula *maxsat_formula){

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

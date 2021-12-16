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

std::pair<PBPred*,PBPred*> VSequential::reify(Lit z, PB * pb){
  vec<Lit> lits;
  vec<int64_t> coeffs;
  int64_t sum = 0;
  for (int i = 0; i < pb->_lits.size(); i++){
    lits.push(~pb->_lits[i]);
    coeffs.push(pb->_coeffs[i]);
    sum += pb->_coeffs[i];
  }
  PB * pb_leq = new PB(lits, coeffs, sum-pb->_rhs+1, _PB_GREATER_OR_EQUAL_);
  pb_leq->addProduct(z, sum-pb->_rhs+1);
  PBPred * pbp_leq = new PBPred(mx->getIncId(), pb_leq, var(z)+1, 1);
  mx->addProofExpr(pbp_leq);
  
  pb->addProduct(~z, pb->_rhs);
  PBPred * pbp_geq = new PBPred(mx->getIncId(), pb, var(z)+1, 0);
  mx->addProofExpr(pbp_geq);
  
  std::pair<PBPred*,PBPred*> res;
  res.first = pbp_geq; // geq
  res.second = pbp_leq; //leq
  return res;
}

int VSequential::derive_sum(vec<PBPred*>& sum){
  if (sum.size() < 2) {
    assert (sum.size() == 1);
    return sum[0]->_ctrid;
  }
  
  int c = sum[0]->_ctrid;
  for (int j = 2; j <= sum.size(); j++){
    
    PBPp * pbp = new PBPp(mx->getIncId());
    // avoid multiplication by 1
    if (j-1 == 1) pbp->addition(c, sum[j-1]->_ctrid);
    else {
      pbp->multiplication(c, j-1);
      pbp->addition(sum[j-1]->_ctrid);
    }
    pbp->division(j);
    mx->addProofExpr(pbp);

    // not needed but may make the proof easier to read
    if (j != sum.size()) c = -1;
    else c = pbp->_ctrid;

  }
  return c;
}

void VSequential::derive_ordering(PBPred* p1, PBPred* p2){
  int d = 0;
  for (int i = 0; i < p1->_ctr->_coeffs.size(); i++){
    if (var(p1->_ctr->_lits[i])+1 != p1->_v)
      d += p1->_ctr->_coeffs[i];
  }
  PBPp * pbp = new PBPp(mx->getIncId());
  pbp->addition(p1->_ctrid, p2->_ctrid);
  pbp->division(d);
  mx->addProofExpr(pbp);
}

std::pair<int,int> VSequential::derive_unary_sum(vec<Lit>& left, vec<Lit>& right, int rhs){
  vec<PBPred*> sum_leq;
  vec<PBPred*> sum_geq;

  for (int j = 0; j < rhs; j++){
      // introduce variables as reification
      // reify(z_j <-> sum^n_i l_i >= j)
      if (j < right.size()){
        vec<int64_t> coeffs;
        coeffs.growTo(left.size(), 1);
        PB * pb = new PB(left, coeffs, j+1, _PB_GREATER_OR_EQUAL_);
        std::pair<PBPred*,PBPred*> p = reify(right[j], pb);
        sum_geq.push(p.first);
        sum_leq.push(p.second);
      }
  }

  // // reverse sum_leq
  vec<PBPred*> sum_leq_rev;
  for (int i = sum_leq.size()-1; i >=0 ; i--){
    sum_leq_rev.push(sum_leq[i]);
  }

  int c_geq = derive_sum(sum_geq);
  int c_leq = derive_sum(sum_leq_rev);

  for (int i = 0; i < rhs-1; i++){
    if (i+1 < sum_geq.size()){
      derive_ordering(sum_leq[i], sum_geq[i+1]);
    }
  }

  std::pair<int,int> res;
  res.first = c_geq;
  res.second = c_leq;

  return res;
}


void VSequential::encode(Card *card, MaxSATFormula *maxsat_formula, pb_Sign sign){
  assert (sign != _PB_EQUAL_);

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
k++; // for proof logging we always treat it as a _PB_LESS_OR_EQUAL_ ctr

// TODO: simplify the cardinality constraint? 
// <= 0 -> all literals are negative; >= n -> all literals are positive  

// TODO: creating some variables that may not be used in the encoding
// Example: if >= we are creating k+1 for the pbp format ; 
// TODO: only create these variables for the pbp format

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

// pbp logging
vec<int> leq;
vec<int> geq;

  for (int i = 1; i <= n; i++){
    int m = i;
    if(k < m) m = k;
    // derive_unary_sum(l_i + sum^m_{i-1},j=1 s_{i-1},j = sum^m_i,j=1 s_i,j)
    vec<Lit> left;
    vec<Lit> right;
    left.push(lits[i-1]);
    for (int j = 1; j <= m; j++){
      right.push(seq_auxiliary[i-1][j-1]);
      if (j != m){ 
        left.push(seq_auxiliary[i-2][j-1]);
      }
    }
    assert (left.size() == right.size());
    std::pair<int,int> res = derive_unary_sum(left, right, k);
    geq.push(res.first);
    leq.push(res.second);
  }

if (current_sign == _PB_GREATER_OR_EQUAL_){
  
  PBPp * pbp = new PBPp(mx->getIncId());
  pbp->addition(card->_id, leq[0]);
  for (int i = 1; i < leq.size(); i++){
    pbp->addition(leq[i]);
  }
  mx->addProofExpr(pbp);
}

if (current_sign == _PB_LESS_OR_EQUAL_){
  PBPp * pbp = new PBPp(mx->getIncId());
  pbp->addition(card->_id, geq[0]);
  for (int i = 1; i < geq.size(); i++){
    pbp->addition(geq[i]);
  }
  mx->addProofExpr(pbp);
}
//end pbp logging

if (current_sign == _PB_GREATER_OR_EQUAL_) k--;

  addBinaryClause(maxsat_formula, ~lits[0], seq_auxiliary[0][0]);
  addBinaryClause(maxsat_formula, lits[0], ~seq_auxiliary[0][0]);

  for (int i = 1; i < n; i++){
    addBinaryClause(maxsat_formula, ~lits[i], seq_auxiliary[i][0]);

    if (i+1 == seq_auxiliary[i].size()){
      addBinaryClause(maxsat_formula, lits[i], ~seq_auxiliary[i][i]);
      addBinaryClause(maxsat_formula, seq_auxiliary[i-1][i-1], ~seq_auxiliary[i][i]);
    }

    for (int j = 0; j < k; j++){
      if (j < seq_auxiliary[i-1].size()) addTernaryClause(maxsat_formula, lits[i], seq_auxiliary[i-1][j],~seq_auxiliary[i][j]);

      if (j < seq_auxiliary[i-1].size()) addBinaryClause(maxsat_formula, ~seq_auxiliary[i-1][j], seq_auxiliary[i][j]);

      if (j+1 < k && j < seq_auxiliary[i-1].size()) addTernaryClause(maxsat_formula, ~lits[i], ~seq_auxiliary[i-1][j], seq_auxiliary[i][j+1]);

      if (i > 1 && j+1 < k && j < seq_auxiliary[i-1].size() && j+1 < seq_auxiliary[i-1].size()){
        addTernaryClause(maxsat_formula, seq_auxiliary[i-1][j], seq_auxiliary[i-1][j+1], ~seq_auxiliary[i][j+1]);
      } 
    }
  }

  if (current_sign == _PB_GREATER_OR_EQUAL_) addUnitClause(maxsat_formula, seq_auxiliary[n-1][k-1]);
  else addUnitClause(maxsat_formula, ~seq_auxiliary[n-1][k-1]);

}

void VSequential::encode(Card *card, MaxSATFormula *maxsat_formula){

  mx = maxsat_formula;
  
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

/*!
 * \author Saurabh Joshi - sbjoshi@iith.ac.in
 *
 * @section LICENSE
 *
 * VeritasPBLib, Copyright (c) 2021, Ruben Martins, Stephan Gocht, Jakob
 * Nordstrom, Andy Oertel
 * Open-WBO, Copyright (c) 2013-2017, Ruben Martins, Vasco Manquinho, Ines Lynce
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

#include "UGTE.h"
#include <algorithm>
#include <numeric>

using namespace openwbo;

struct less_than_wlitt {
  inline bool operator()(const wlitt &wl1, const wlitt &wl2) {
    return (wl1.weight < wl2.weight);
  }
};

weightedlitst UGTE::sort_to_list(wlit_mapt &map) {
  weightedlitst list;
  wlitt wl;
  wl.weight = 0;
  wl.lit = map.end()->second;
  list.push_back(wl);
  for (wlit_mapt::iterator it = map.begin(); it != map.end(); it++) {
    wlitt wl;
    wl.lit = it->second;
    wl.weight = it->first;
    list.push_back(wl);
  }
  less_than_wlitt lt_wlit;
  std::sort(list.begin(), list.end(), lt_wlit);
  return list;
}
// create new literal
Lit UGTE::getNewLit(MaxSATFormula *maxsat_formula) {
  Lit p = mkLit(maxsat_formula->nVars(), false);
  maxsat_formula->newVar();
  return p;
}

// get variable with `weight` (coefficient) from the output literals used for
// the clauses (variables used in the PB constraint and fresh variables)
Lit UGTE::get_var(MaxSATFormula *maxsat_formula, wlit_mapt &oliterals,
                  uint64_t weight) {
  wlit_mapt::iterator it = oliterals.find(weight);
  if (it == oliterals.end()) {
    Lit v = getNewLit(maxsat_formula);
    oliterals[weight] = v;
  }
  return oliterals[weight];
}

uint64_t UGTE::succ(wlit_mapt &literals, uint64_t weight) {
  uint64_t succ_weight = UINT64_MAX;
  for (wlit_mapt::iterator it = literals.begin(); it != literals.end(); it++) {
    if (it->first > weight && it->first < succ_weight) {
      succ_weight = it->first;
    }
  }
  assert(succ_weight != UINT64_MAX);
  return succ_weight;
}

// recursive algorithm that actually encodes the PB constraint
bool UGTE::encodeLeq(uint64_t k, MaxSATFormula *maxsat_formula, PB *pb,
                     const weightedlitst &iliterals, wlit_mapt &oliterals) {
  if (iliterals.size() == 0 || k == 0)
    return false;

  if (iliterals.size() == 1) {
    oliterals.insert(
        wlit_pairt(iliterals.front().weight, iliterals.front().lit));
    return true;
  }

  unsigned int size = iliterals.size();

  weightedlitst linputs, rinputs;
  wlit_mapt loutputs, routputs;

  // split input literals in half
  unsigned int lsize = size >> 1;
  weightedlitst::const_iterator myit = iliterals.begin();
  weightedlitst::const_iterator myit1 = myit + lsize;
  weightedlitst::const_iterator myit2 = iliterals.end();
  linputs.insert(linputs.begin(), myit, myit1);
  rinputs.insert(rinputs.begin(), myit1, myit2);

  // bound output to rhs
  wlit_sumt wlit_sum;
  uint64_t lk =
      std::accumulate(linputs.begin(), linputs.end(), uint64_t(0), wlit_sum);
  uint64_t rk =
      std::accumulate(rinputs.begin(), rinputs.end(), uint64_t(0), wlit_sum);
  lk = k >= lk ? lk : k;
  rk = k >= rk ? rk : k;

  // process recursion (with fresh constructed left and right literals)
  // -> literal lists are different for each call
  bool result = encodeLeq(lk, maxsat_formula, pb, linputs, loutputs);
  if (!result)
    return result;
  result = result && encodeLeq(rk, maxsat_formula, pb, rinputs, routputs);
  if (!result)
    return result;

  // bind output literals to literals that represent a sum of at least the coeff
  {
    assert(!loutputs.empty());

    for (wlit_mapt::iterator left_it = loutputs.begin();
         left_it != loutputs.end(); left_it++) {
      addBinaryClause(maxsat_formula, pb, ~left_it->second,
                      get_var(maxsat_formula, oliterals, left_it->first));
    }
  }

  {
    assert(!routputs.empty());

    for (wlit_mapt::iterator right_it = routputs.begin();
         right_it != routputs.end(); right_it++) {
      addBinaryClause(maxsat_formula, pb, ~right_it->second,
                      get_var(maxsat_formula, oliterals, right_it->first));
    }
  }

  // for each combination of values from left and right side
  for (wlit_mapt::iterator lit = loutputs.begin(); lit != loutputs.end();
       lit++) {
    for (wlit_mapt::iterator rit = routputs.begin(); rit != routputs.end();
         rit++) {
      uint64_t tw = lit->first + rit->first;
      addTernaryClause(maxsat_formula, pb, ~lit->second, ~rit->second,
                       get_var(maxsat_formula, oliterals, tw));
    }
  }

  // clauses for geq constraints
  weightedlitst left_list = sort_to_list(loutputs);
  weightedlitst right_list = sort_to_list(routputs);
  uint64_t left_max = left_list[left_list.size() - 1].weight;
  uint64_t right_max = right_list[right_list.size() - 1].weight;

  uint64_t prev_weight = 0;
  for (uint i = 1; i < left_list.size(); i++) {
    addBinaryClause(maxsat_formula, pb, left_list[i].lit,
                    ~get_var(maxsat_formula, oliterals,
                             succ(oliterals, prev_weight + right_max)));
    prev_weight = left_list[i].weight;
  }

  prev_weight = 0;
  for (uint j = 1; j < right_list.size(); j++) {
    addBinaryClause(maxsat_formula, pb, right_list[j].lit,
                    ~get_var(maxsat_formula, oliterals,
                             succ(oliterals, prev_weight + left_max)));
    prev_weight = right_list[j].weight;
  }

  uint64_t prev_left_weight = 0;
  for (uint i = 1; i < left_list.size(); i++) {
    uint64_t prev_right_weight = 0;
    for (uint j = 1; j < right_list.size(); j++) {
      uint64_t tw = prev_left_weight + prev_right_weight;
      addTernaryClause(
          maxsat_formula, pb, left_list[i].lit, right_list[j].lit,
          ~get_var(maxsat_formula, oliterals, succ(oliterals, tw)));
      prev_right_weight = right_list[j].weight;
    }
    prev_left_weight = left_list[i].weight;
  }

  // k-simplification
  uint64_t max_lit_weight = UINT64_MAX;
  vec<uint64_t> weights_to_remove;
  for (wlit_mapt::iterator lit = oliterals.begin(); lit != oliterals.end();
       lit++) {
    if (lit->first >= k && lit->first < max_lit_weight) {
      weights_to_remove.push(max_lit_weight);
      max_lit_weight = lit->first;
    }
    if (lit->first > max_lit_weight) {
      weights_to_remove.push(lit->first);
    }
  }
  for (int i = 0; i < weights_to_remove.size(); i++) {
    oliterals.erase(weights_to_remove[i]);
  }

  return true;
}

// copies the current PB constraint into new vectors
void UGTE::encode(PB *pb, MaxSATFormula *maxsat_formula, pb_Sign current_sign) {
  vec<Lit> lits;
  uint64_t sum = 0;
  pb->_lits.copyTo(lits);

  vec<uint64_t> coeffs;
  for (int i = 0; i < pb->_coeffs.size(); i++) {
    assert(pb->_coeffs[i] > 0);
    coeffs.push(pb->_coeffs[i]);
    sum += pb->_coeffs[i];
  }
  uint64_t rhs = pb->_rhs;

  // simplifications
  // all literals must be assigned to 0
  if (rhs == 0 && current_sign == _PB_LESS_OR_EQUAL_) {
    for (int i = 0; i < lits.size(); i++) {
      addUnitClause(maxsat_formula, pb, ~lits[i]);
    }
    return;
  }
  // all literals must be assigned to 1
  if (rhs == sum && current_sign == _PB_GREATER_OR_EQUAL_) {
    for (int i = 0; i < lits.size(); i++) {
      addUnitClause(maxsat_formula, pb, lits[i]);
    }
    return;
  }
  // constraint is no restriction
  if (rhs == sum && current_sign == _PB_LESS_OR_EQUAL_) {
    return;
  }
  if (rhs == 0 && current_sign == _PB_GREATER_OR_EQUAL_) {
    return;
  }

  // transform the constraint to consider the smallest rhs
  if (sum - rhs < rhs) {
    for (int i = 0; i < lits.size(); i++) {
      lits[i] = ~(lits[i]);
    }
    rhs = sum - rhs;
    if (current_sign != _PB_EQUAL_) {
      if (current_sign == _PB_GREATER_OR_EQUAL_)
        current_sign = _PB_LESS_OR_EQUAL_;
      else
        current_sign = _PB_GREATER_OR_EQUAL_;
    }
  }

  encode(maxsat_formula, pb, lits, coeffs, rhs, current_sign);
}

void UGTE::encode(MaxSATFormula *maxsat_formula, PB *pb, vec<Lit> &lits,
                  vec<uint64_t> &coeffs, uint64_t rhs, pb_Sign current_sign) {
  if (rhs >= UINT64_MAX) {
    printf("c Overflow in the Encoding\n");
    printf("s UNKNOWN\n");
    exit(_ERROR_);
  }

  vec<Lit> simp_lits;
  vec<uint64_t> simp_coeffs;
  lits.copyTo(simp_lits);
  coeffs.copyTo(simp_coeffs);

  lits.clear();
  coeffs.clear();

  // Fix literals that have a coeff larger than rhs.
  for (int i = 0; i < simp_lits.size(); i++) {
    if (simp_coeffs[i] == 0)
      continue;

    if (simp_coeffs[i] >= UINT64_MAX) {
      printf("c Overflow in the Encoding\n");
      printf("s UNKNOWN\n");
      exit(_ERROR_);
    }

    if (simp_coeffs[i] > (unsigned)rhs && current_sign == _PB_LESS_OR_EQUAL_) {
      addUnitClause(maxsat_formula, pb, ~simp_lits[i]);
    } else {
      lits.push(simp_lits[i]);
      coeffs.push(simp_coeffs[i]);
    }
  }

  if (lits.size() == 0)
    return;

  weightedlitst iliterals;
  for (int i = 0; i < lits.size(); i++) {
    wlitt wl;
    wl.lit = lits[i];
    wl.weight = coeffs[i];
    iliterals.push_back(wl);
  }
  less_than_wlitt lt_wlit;
  std::sort(iliterals.begin(), iliterals.end(), lt_wlit);
  if (current_sign == _PB_GREATER_OR_EQUAL_) {
    encodeLeq(rhs, maxsat_formula, pb, iliterals, pb_oliterals);
  } else {
    encodeLeq(rhs + 1, maxsat_formula, pb, iliterals, pb_oliterals);
  }

  weightedlitst out_list = sort_to_list(pb_oliterals);
  if (current_sign == _PB_LESS_OR_EQUAL_ || current_sign == _PB_EQUAL_) {
    for (uint i = out_list.size() - 1; i >= 0; i--) {
      if (out_list[i].weight > rhs) {
        addUnitClause(maxsat_formula, pb, ~out_list[i].lit);
      } else {
        break;
      }
    }
  }
  if (current_sign == _PB_GREATER_OR_EQUAL_ || current_sign == _PB_EQUAL_) {
    for (uint i = out_list.size() - 1; i >= 0; i--) {
      if (out_list[i].weight >= rhs) {
        addUnitClause(maxsat_formula, pb, out_list[i].lit);
      } else {
        break;
      }
    }
  }
}

void UGTE::encode(PB *pb, MaxSATFormula *maxsat_formula) {
  mx = maxsat_formula;

  switch (pb->_sign) {
  case _PB_EQUAL_:
    encode(pb, maxsat_formula, _PB_EQUAL_);
    break;
  case _PB_LESS_OR_EQUAL_:
    encode(pb, maxsat_formula, _PB_LESS_OR_EQUAL_);
    break;
  case _PB_GREATER_OR_EQUAL_:
    encode(pb, maxsat_formula, _PB_GREATER_OR_EQUAL_);
    break;
  default:
    assert(false);
  }
}
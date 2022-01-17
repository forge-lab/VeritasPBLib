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

#include "VGTE.h"
#include <algorithm>
#include <numeric>
using namespace openwbo;

struct less_than_wlitt {
  inline bool operator()(const wlitt &wl1, const wlitt &wl2) {
    return (wl1.weight < wl2.weight);
  }
};

// create new literal
Lit VGTE::getNewLit(MaxSATFormula *maxsat_formula) {
  Lit p = mkLit(maxsat_formula->nVars(), false);
  maxsat_formula->newVar();
  return p;
}

// get variable with `weight` (coefficient) from the output literals used for
// the clauses (variables used in the PB constraint and fresh variables)
Lit VGTE::get_var(MaxSATFormula *maxsat_formula, wlit_mapt &oliterals,
                  uint64_t weight) {
  wlit_mapt::iterator it = oliterals.find(weight);
  if (it == oliterals.end()) {
    Lit v = getNewLit(maxsat_formula);
    oliterals[weight] = v;
  }
  return oliterals[weight];
}

// recursive algorithm that actually encodes the PB constraint
bool VGTE::encodeLeq(uint64_t k, MaxSATFormula *maxsat_formula,
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
  bool result = encodeLeq(lk, maxsat_formula, linputs, loutputs);
  if (!result)
    return result;
  result = result && encodeLeq(rk, maxsat_formula, rinputs, routputs);
  if (!result)
    return result;

  // bind output literals to literals that represent a sum of at least the coeff
  {
    assert(!loutputs.empty());

    for (wlit_mapt::iterator left_it = loutputs.begin();
         left_it != loutputs.end(); left_it++) {

      if (left_it->first > k) {
        addBinaryClause(maxsat_formula, ~left_it->second,
                        get_var(maxsat_formula, oliterals, k));
      } else {
        addBinaryClause(maxsat_formula, ~left_it->second,
                        get_var(maxsat_formula, oliterals, left_it->first));
      }
    }
  }

  {
    assert(!routputs.empty());

    for (wlit_mapt::iterator right_it = routputs.begin();
         right_it != routputs.end(); right_it++) {

      if (right_it->first > k) {
        addBinaryClause(maxsat_formula, ~right_it->second,
                        get_var(maxsat_formula, oliterals, k));
      } else {
        addBinaryClause(maxsat_formula, ~right_it->second,
                        get_var(maxsat_formula, oliterals, right_it->first));
      }
    }
  }

  // for each combination of values from left and right side
  for (wlit_mapt::iterator lit = loutputs.begin(); lit != loutputs.end();
       lit++) {
    for (wlit_mapt::iterator rit = routputs.begin(); rit != routputs.end();
         rit++) {
      uint64_t tw = lit->first + rit->first;
      if (tw > k) {
        addTernaryClause(maxsat_formula, ~lit->second, ~rit->second,
                         get_var(maxsat_formula, oliterals, k));
      } else {
        addTernaryClause(maxsat_formula, ~lit->second, ~rit->second,
                         get_var(maxsat_formula, oliterals, tw));
      }
    }
  }

  return true;
}

void VGTE::encode(PB *pb, MaxSATFormula *maxsat_formula) {
  mx = maxsat_formula;

  switch (pb->_sign) {
  case _PB_EQUAL_:
    encode(pb, maxsat_formula, _PB_GREATER_OR_EQUAL_);
    encode(pb, maxsat_formula, _PB_LESS_OR_EQUAL_);
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

// copies the current PB constraint into new vectors
void VGTE::encode(PB *pb, MaxSATFormula *maxsat_formula, pb_Sign sign) {
  assert(sign != _PB_EQUAL_);
  vec<Lit> lits;
  pb->_lits.copyTo(lits);

  vec<uint64_t> coeffs;
  for (int i = 0; i < pb->_coeffs.size(); i++) {
    assert(pb->_coeffs[i] > 0);
    coeffs.push(pb->_coeffs[i]);
  }
  uint64_t rhs = pb->_rhs;

  // transform it into <=
  if (sign == _PB_GREATER_OR_EQUAL_) {
    int s = 0;
    for (int i = 0; i < coeffs.size(); i++) {
      s += coeffs[i];
      lits[i] = ~(lits[i]);
    }
    rhs = s - rhs;
  }

  encode(maxsat_formula, lits, coeffs, rhs);
}

void VGTE::encode(MaxSATFormula *maxsat_formula, vec<Lit> &lits,
                  vec<uint64_t> &coeffs, uint64_t rhs) {
  // FIXME: do not change coeffs in this method. Make coeffs const.

  // If the rhs is larger than INT32_MAX is not feasible to encode this
  // pseudo-Boolean constraint to CNF.
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

    if (simp_coeffs[i] <= (unsigned)rhs) {
      lits.push(simp_lits[i]);
      coeffs.push(simp_coeffs[i]);
    } else
      addUnitClause(maxsat_formula, ~simp_lits[i]);
  }

  if (lits.size() == 1) {
    // addUnitClause(S, ~lits[0]);
    return;
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
  encodeLeq(rhs + 1, maxsat_formula, iliterals, pb_oliterals);

  for (wlit_mapt::reverse_iterator rit = pb_oliterals.rbegin();
       rit != pb_oliterals.rend(); rit++) {
    if (rit->first > rhs) {
      addUnitClause(maxsat_formula, ~rit->second);
    } else {
      break;
    }
  }

  current_pb_rhs = rhs;
}
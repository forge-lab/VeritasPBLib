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

// left...A, right...B
void VGTE::try_all_values(PB *pb, weightedlitst &left, weightedlitst &right,
                          Lit &z_eq) {
  int constr_outer_id = 0;
  for (uint left_i = 0; left_i < left.size(); left_i++) {
    int constr_inner_id = 0;
    for (uint right_i = 0; right_i < right.size(); right_i++) {
      vec<Lit> lits;
      lits.push(z_eq);
      if (left_i > 0) {
        lits.push(~left[left_i].lit);
      }
      if (right_i > 0) {
        lits.push(~right[right_i].lit);
      }
      if (left_i < left.size() - 1) {
        lits.push(left[left_i + 1].lit);
      }
      if (right_i < right.size() - 1) {
        lits.push(right[right_i + 1].lit);
      }
      PBPu *pbp_single_try = new PBPu(mx->getIncProofLogId(), lits);
      mx->addProofExpr(pb, pbp_single_try);
      if (constr_inner_id) {
        PBPp *pbp_inner = new PBPp(mx->getIncProofLogId());
        pbp_inner->addition(constr_inner_id, pbp_single_try->_ctrid);
        mx->addProofExpr(pb, pbp_inner);
        constr_inner_id = pbp_inner->_ctrid;
      } else {
        constr_inner_id = pbp_single_try->_ctrid;
      }
    }
    PBPp *pbp_outer = new PBPp(mx->getIncProofLogId());
    pbp_outer->saturation(constr_inner_id);
    if (constr_outer_id) {
      pbp_outer->addition(constr_outer_id);
    }
    mx->addProofExpr(pb, pbp_outer);
    constr_outer_id = pbp_outer->_ctrid;
  }
  PBPp *pbp_final = new PBPp(mx->getIncProofLogId());
  pbp_final->saturation(constr_outer_id);
  mx->addProofExpr(pb, pbp_final);
}

weightedlitst VGTE::sort_to_list(wlit_mapt &map) {
  weightedlitst list;
  wlitt wl;
  wl.weight = 0;
  wl.lit = lit_Undef;
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

std::pair<int, int> VGTE::derive_sparse_unary_sum(MaxSATFormula *maxsat_formula,
                                                  PB *pb, wlit_mapt &left,
                                                  wlit_mapt &right,
                                                  wlit_mapt &current) {
  // construct left hand site of the preserving equality
  vec<int64_t> coeffs;
  vec<Lit> lits;
  weightedlitst left_list = sort_to_list(left);
  weightedlitst right_list = sort_to_list(right);
  weightedlitst current_list = sort_to_list(current);
  int64_t weight_prev = 0;
  for (uint i = 1; i < left_list.size(); i++) {
    coeffs.push(left_list[i].weight - weight_prev);
    lits.push(left_list[i].lit);
    weight_prev = left_list[i].weight;
  }
  weight_prev = 0;
  for (uint i = 1; i < right_list.size(); i++) {
    coeffs.push(right_list[i].weight - weight_prev);
    lits.push(right_list[i].lit);
    weight_prev = right_list[i].weight;
  }

  // log ordering
  PBPred *p_prev = NULL;
  for (wlit_mapt::iterator current_it = current.begin();
       current_it != current.end(); current_it++) {
    PB *pb_single_var =
        new PB(lits, coeffs, current_it->first, _PB_GREATER_OR_EQUAL_);
    std::pair<PBPred *, PBPred *> p =
        reify(pb, current_it->second, pb_single_var);
    if (p_prev != NULL) {
      assert(p_prev);
      derive_ordering(pb, p_prev, p.first);
    }
    p_prev = p.second;
  }

  // reify constraints to be derived
  weight_prev = 0;
  for (weightedlitst::iterator current_it = current_list.begin();
       current_it != current_list.end(); current_it++) {
    coeffs.push(current_it->weight - weight_prev);
    lits.push(~current_it->lit);
    weight_prev = current_it->weight;
  }
  Lit z_geq = getNewLit(maxsat_formula);
  PB *pb_full_geq = new PB(lits, coeffs, weight_prev, _PB_GREATER_OR_EQUAL_);
  std::pair<PBPred *, PBPred *> p_geq = reify(pb, z_geq, pb_full_geq);

  int64_t sum = 0;
  for (int i = 0; i < lits.size(); i++) {
    lits[i] = ~lits[i];
    sum += coeffs[i];
  }
  Lit z_leq = getNewLit(maxsat_formula);
  PB *pb_full_leq =
      new PB(lits, coeffs, sum - weight_prev, _PB_GREATER_OR_EQUAL_);
  std::pair<PBPred *, PBPred *> p_leq = reify(pb, z_leq, pb_full_leq);

  Lit z_eq = getNewLit(maxsat_formula);
  vec<int64_t> coeffs_eq;
  vec<Lit> lits_eq;
  coeffs_eq.growTo(2, 1);
  lits_eq.push(z_geq);
  lits_eq.push(z_leq);
  PB *pb_full_eq = new PB(lits_eq, coeffs_eq, 2, _PB_GREATER_OR_EQUAL_);
  reify(pb, z_eq, pb_full_eq);

  try_all_values(pb, left_list, right_list, z_eq);

  // derive constraint to be derived from its reification
  uint64_t sum_max = left_list[left_list.size() - 1].weight +
                     right_list[right_list.size() - 1].weight;
  vec<Lit> lits_geq;
  lits_geq.push(z_geq);
  PBPu *pbp_rup_geq = new PBPu(mx->getIncProofLogId(), lits_geq);
  mx->addProofExpr(pb, pbp_rup_geq);
  PBPp *pbp_p_geq = new PBPp(mx->getIncProofLogId());
  pbp_p_geq->multiplication(pbp_rup_geq->_ctrid, sum_max);
  pbp_p_geq->addition(p_geq.first->_ctrid);
  mx->addProofExpr(pb, pbp_p_geq);

  vec<Lit> lits_leq;
  lits_leq.push(z_leq);
  PBPu *pbp_rup_leq = new PBPu(mx->getIncProofLogId(), lits_leq);
  mx->addProofExpr(pb, pbp_rup_leq);
  PBPp *pbp_p_leq = new PBPp(mx->getIncProofLogId());
  pbp_p_leq->multiplication(pbp_rup_leq->_ctrid, sum_max);
  pbp_p_leq->addition(p_leq.first->_ctrid);
  mx->addProofExpr(pb, pbp_p_leq);

  std::pair<int, int> res;
  res.first = pbp_p_geq->_ctrid;
  res.second = pbp_p_leq->_ctrid;
  return res;
}

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

uint64_t VGTE::succ(wlit_mapt &literals, uint64_t weight) {
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
bool VGTE::encodeLeq(uint64_t k, MaxSATFormula *maxsat_formula, PB *pb,
                     const weightedlitst &iliterals, wlit_mapt &oliterals,
                     vec<int> &geq, vec<int> &leq) {
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
  bool result = encodeLeq(lk, maxsat_formula, pb, linputs, loutputs, geq, leq);
  if (!result)
    return result;
  result =
      result && encodeLeq(rk, maxsat_formula, pb, rinputs, routputs, geq, leq);
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

  std::pair<int, int> res_pair = derive_sparse_unary_sum(
      maxsat_formula, pb, loutputs, routputs, oliterals);
  geq.push(res_pair.first);
  leq.push(res_pair.second);

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
void VGTE::encode(PB *pb, MaxSATFormula *maxsat_formula, pb_Sign current_sign) {
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
  bool flipped = false;
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
    flipped = true;
  }

  encode(maxsat_formula, pb, lits, coeffs, rhs, current_sign, flipped);
}

void VGTE::encode(MaxSATFormula *maxsat_formula, PB *pb, vec<Lit> &lits,
                  vec<uint64_t> &coeffs, uint64_t rhs, pb_Sign current_sign,
                  bool flipped) {
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
  vec<int> geq;
  vec<int> leq;
  if (current_sign == _PB_GREATER_OR_EQUAL_) {
    encodeLeq(rhs, maxsat_formula, pb, iliterals, pb_oliterals, geq, leq);
  } else {
    encodeLeq(rhs + 1, maxsat_formula, pb, iliterals, pb_oliterals, geq, leq);
  }

  // begin proof log output
  if (current_sign == _PB_LESS_OR_EQUAL_ || current_sign == _PB_EQUAL_) {
    if (geq.size() != 0) {
      PBPp *pbp_output_leq = new PBPp(mx->getIncProofLogId());
      if (current_sign == _PB_EQUAL_ && !flipped) {
        pbp_output_leq->addition(pb->_id + 1, geq[0]);
      } else {
        pbp_output_leq->addition(pb->_id, geq[0]);
      }
      for (int i = 1; i < geq.size(); i++) {
        pbp_output_leq->addition(geq[i]);
      }
      mx->addProofExpr(pb, pbp_output_leq);
    }
  }
  if (current_sign == _PB_GREATER_OR_EQUAL_ || current_sign == _PB_EQUAL_) {
    if (leq.size() != 0) {
      PBPp *pbp_output_geq = new PBPp(mx->getIncProofLogId());
      if (current_sign == _PB_EQUAL_ && flipped) {
        pbp_output_geq->addition(pb->_id + 1, leq[0]);
      } else {
        pbp_output_geq->addition(pb->_id, leq[0]);
      }
      for (int i = 1; i < leq.size(); i++) {
        pbp_output_geq->addition(leq[i]);
      }
      mx->addProofExpr(pb, pbp_output_geq);
    }
  }
  // end proof log output

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
    for (uint i = 1; i < out_list.size(); i++) {
      if (out_list[i].weight <= rhs) {
        addUnitClause(maxsat_formula, pb, out_list[i].lit);
      } else {
        if (i > 1 && current_sign == _PB_EQUAL_ &&
            out_list[i - 1].weight != rhs) {
          addUnitClause(maxsat_formula, pb, out_list[i].lit);
        }
        break;
      }
    }
  }
}

void VGTE::encode(PB *pb, MaxSATFormula *maxsat_formula) {
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
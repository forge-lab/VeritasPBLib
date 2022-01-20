/*!
 * \author Ruben Martins - rubenm@andrew.cmu.edu
 *
 * @section LICENSE
 *
 * VeritasPBLib, Copyright (c) 2021, Ruben Martins, Stephan Gocht, Jakob
 * Nordstrom
 * PBLib,    Copyright (c) 2012-2013  Peter Steinke
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

#include "VAdder.h"
#include <algorithm>

using namespace openwbo;

void VAdder::FA_extra(MaxSATFormula *maxsat_formula, Lit xc, Lit xs, Lit a,
                      Lit b, Lit c) {

  clause.clear();
  addTernaryClause(maxsat_formula, ~xc, ~xs, a);
  addTernaryClause(maxsat_formula, ~xc, ~xs, b);
  addTernaryClause(maxsat_formula, ~xc, ~xs, c);

  addTernaryClause(maxsat_formula, xc, xs, ~a);
  addTernaryClause(maxsat_formula, xc, xs, ~b);
  addTernaryClause(maxsat_formula, xc, xs, ~c);
}

Lit VAdder::FA_carry(MaxSATFormula *maxsat_formula, Lit a, Lit b, Lit c) {
  Lit carry = mkLit(maxsat_formula->nVars(), false);
  maxsat_formula->newVar();

  addTernaryClause(maxsat_formula, b, c, ~carry);
  addTernaryClause(maxsat_formula, a, c, ~carry);
  addTernaryClause(maxsat_formula, a, b, ~carry);

  addTernaryClause(maxsat_formula, ~b, ~c, carry);
  addTernaryClause(maxsat_formula, ~a, ~c, carry);
  addTernaryClause(maxsat_formula, ~a, ~b, carry);

  return carry;
}

Lit VAdder::FA_sum(MaxSATFormula *maxsat_formula, Lit a, Lit b, Lit c) {
  Lit sum = mkLit(maxsat_formula->nVars(), false);
  maxsat_formula->newVar();

  addQuaternaryClause(maxsat_formula, a, b, c, ~sum);
  addQuaternaryClause(maxsat_formula, a, ~b, ~c, ~sum);
  addQuaternaryClause(maxsat_formula, ~a, b, ~c, ~sum);
  addQuaternaryClause(maxsat_formula, ~a, ~b, c, ~sum);

  addQuaternaryClause(maxsat_formula, ~a, ~b, ~c, sum);
  addQuaternaryClause(maxsat_formula, ~a, b, c, sum);
  addQuaternaryClause(maxsat_formula, a, ~b, c, sum);
  addQuaternaryClause(maxsat_formula, a, b, ~c, sum);

  return sum;
}

Lit VAdder::HA_carry(MaxSATFormula *maxsat_formula, Lit a, Lit b) {
  Lit carry = mkLit(maxsat_formula->nVars(), false);
  maxsat_formula->newVar();

  addBinaryClause(maxsat_formula, a, ~carry);
  addBinaryClause(maxsat_formula, b, ~carry);
  addTernaryClause(maxsat_formula, ~a, ~b, carry);

  return carry;
}

Lit VAdder::HA_sum(MaxSATFormula *maxsat_formula, Lit a, Lit b) {
  Lit sum = mkLit(maxsat_formula->nVars(), false);
  maxsat_formula->newVar();

  addTernaryClause(maxsat_formula, ~a, ~b, ~sum);
  addTernaryClause(maxsat_formula, a, b, ~sum);

  addTernaryClause(maxsat_formula, ~a, b, sum);
  addTernaryClause(maxsat_formula, a, ~b, sum);

  return sum;
}

void VAdder::adderTree(MaxSATFormula *maxsat_formula,
                       std::vector<std::queue<Lit>> &buckets, vec<Lit> &result,
                       int pb_id, uint64_t log_k) {
  Lit x, y, z;
  Lit u = lit_Undef;
  int current_constr_id = pb_id;

  for (size_t i = 0; i < log_k && i < buckets.size(); i++) {
    if (buckets[i].size() == 0)
      continue;

    if (i == buckets.size() - 1 && buckets[i].size() >= 2) {
      buckets.push_back(std::queue<Lit>());
      result.push(u);
    }

    std::pair<PBPred *, PBPred *> pair_carry;
    std::pair<PBPred *, PBPred *> pair_sum;

    while (buckets[i].size() >= 3) {
      x = buckets[i].front();
      buckets[i].pop();
      y = buckets[i].front();
      buckets[i].pop();
      z = buckets[i].front();
      buckets[i].pop();
      Lit x_carry = FA_carry(maxsat_formula, x, y, z);
      Lit x_sum = FA_sum(maxsat_formula, x, y, z);
      buckets[i + 1].push(x_carry);
      buckets[i].push(x_sum);
      FA_extra(maxsat_formula, x_carry, x_sum, x, y, z);

      // proof log the full adder
      vec<Lit> pb_lits_carry;
      pb_lits_carry.push(x);
      pb_lits_carry.push(y);
      pb_lits_carry.push(z);
      vec<int64_t> coeffs_carry(3, 1);
      PB *pb_carry =
          new PB(pb_lits_carry, coeffs_carry, 2, _PB_GREATER_OR_EQUAL_);
      pair_carry = reify(x_carry, pb_carry);

      vec<Lit> pb_lits_sum;
      pb_lits_sum.push(x);
      pb_lits_sum.push(y);
      pb_lits_sum.push(z);
      pb_lits_sum.push(~x_carry);
      vec<int64_t> coeffs_sum(3, 1);
      coeffs_sum.push(2);
      PB *pb_sum = new PB(pb_lits_sum, coeffs_sum, 3, _PB_GREATER_OR_EQUAL_);
      pair_sum = reify(x_sum, pb_sum);

      PBPp *pbp_geq = new PBPp(mx->getIncProofLogId());
      pbp_geq->multiplication(pair_carry.first->_ctrid, 2);
      pbp_geq->addition(pair_sum.first->_ctrid);
      pbp_geq->division(3);
      mx->addProofExpr(pbp_geq);
      PBPp *pbp_geq_sum = new PBPp(mx->getIncProofLogId());
      pbp_geq_sum->multiplication(pbp_geq->_ctrid, 1 << i);
      pbp_geq_sum->addition(current_constr_id);
      mx->addProofExpr(pbp_geq_sum);
      current_constr_id = pbp_geq_sum->_ctrid;
    }

    if (buckets[i].size() == 2) {
      x = buckets[i].front();
      buckets[i].pop();
      y = buckets[i].front();
      buckets[i].pop();
      Lit x_carry = HA_carry(maxsat_formula, x, y);
      Lit x_sum = HA_sum(maxsat_formula, x, y);
      buckets[i + 1].push(x_carry);
      buckets[i].push(x_sum);

      // proof logging for half adder
      vec<Lit> pb_lits_carry;
      pb_lits_carry.push(x);
      pb_lits_carry.push(y);
      vec<int64_t> coeffs_carry(2, 1);
      PB *pb_carry =
          new PB(pb_lits_carry, coeffs_carry, 2, _PB_GREATER_OR_EQUAL_);
      pair_carry = reify(x_carry, pb_carry);

      vec<Lit> pb_lits_sum;
      pb_lits_sum.push(x);
      pb_lits_sum.push(y);
      pb_lits_sum.push(~x_carry);
      vec<int64_t> coeffs_sum(2, 1);
      coeffs_sum.push(2);
      PB *pb_sum = new PB(pb_lits_sum, coeffs_sum, 3, _PB_GREATER_OR_EQUAL_);
      pair_sum = reify(x_sum, pb_sum);

      PBPp *pbp_geq = new PBPp(mx->getIncProofLogId());
      pbp_geq->multiplication(pair_carry.first->_ctrid, 2);
      pbp_geq->addition(pair_sum.first->_ctrid);
      pbp_geq->division(3);
      mx->addProofExpr(pbp_geq);
      PBPp *pbp_geq_sum = new PBPp(mx->getIncProofLogId());
      pbp_geq_sum->multiplication(pbp_geq->_ctrid, 1 << i);
      pbp_geq_sum->addition(current_constr_id);
      mx->addProofExpr(pbp_geq_sum);
      current_constr_id = pbp_geq_sum->_ctrid;
    }

    result[i] = buckets[i].front();
    buckets[i].pop();
  }
}

// Generates clauses for “xs <= ys”, assuming ys has only constant signals (0 or
// 1). xs and ys must have the same size

void VAdder::lessThanOrEqual(MaxSATFormula *maxsat_formula, vec<Lit> &xs,
                             std::vector<uint64_t> &ys) {
  assert((size_t)xs.size() == ys.size());
  vec<Lit> clause;
  bool skip;
  for (int i = 0; i < xs.size(); ++i) {
    if (ys[i] == 1 || xs[i] == lit_Undef)
      continue;

    clause.clear();

    skip = false;

    for (int j = i + 1; j < xs.size(); ++j) {
      if (ys[j] == 1) {
        if (xs[j] == lit_Undef) {
          skip = true;
          break;
        }

        clause.push(~xs[j]);
      } else {
        assert(ys[j] == 0);

        if (xs[j] == lit_Undef)
          continue;

        clause.push(xs[j]);
      }
    }

    if (skip)
      continue;

    clause.push(~xs[i]);

    addClause(maxsat_formula, clause);
  }
}

void VAdder::numToBits(std::vector<uint64_t> &bits, uint64_t n,
                       uint64_t number) {
  bits.clear();

  for (int64_t i = n - 1; i >= 0; --i) {
    uint64_t tmp = ((uint64_t)1) << i;
    if (number < tmp) {
      bits.push_back(0);
    } else {
      bits.push_back(1);
      number -= tmp;
    }
  }

  reverse(bits.begin(), bits.end());
}

void VAdder::encode(PB *pb, MaxSATFormula *maxsat_formula) {
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

void VAdder::encode(PB *pb, MaxSATFormula *maxsat_formula, pb_Sign sign) {
  assert(sign != _PB_EQUAL_);

  vec<Lit> lits;
  vec<uint64_t> coeffs;

  pb->_lits.copyTo(lits);
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

  int pb_id = pb->_id;

  // TODO: should we simplify the PB constraint?

  encode(maxsat_formula, lits, coeffs, rhs, sign, pb_id);
}

void VAdder::encode(MaxSATFormula *maxsat_formula, vec<Lit> &lits,
                    vec<uint64_t> &coeffs, uint64_t rhs, pb_Sign sign,
                    int pb_id) {
  _output.clear();

  uint64_t nb = ld64(rhs); // number of bits
  Lit u = lit_Undef;

  for (uint64_t iBit = 0; iBit <= nb; ++iBit) {
    _buckets.push_back(std::queue<Lit>());
    _output.push(u);
    for (int iVar = 0; iVar < lits.size(); ++iVar) {
      if (((((int64_t)1) << iBit) & coeffs[iVar]) != 0)
        _buckets.back().push(lits[iVar]);
    }
  }

  adderTree(maxsat_formula, _buckets, _output, pb_id, nb);

  for (uint64_t i = nb; i < _buckets.size(); i++) {
    while (_buckets[i].size() > 0) {
      addUnitClause(maxsat_formula, ~_buckets[i].front());
      _buckets[i].pop();
    }
  }

  std::vector<uint64_t> kBits;
  numToBits(kBits, _buckets.size(), rhs);

  lessThanOrEqual(maxsat_formula, _output, kBits);
}

uint64_t VAdder::ld64(const uint64_t x) {
  return (sizeof(uint64_t) << 3) - __builtin_clzll(x);
}

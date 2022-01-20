/*!
 * \author Ruben Martins - rubenm@andrew.cmu.edu
 *
 * @section LICENSE
 *
 * VeritasPBLib, Copyright (c) 2021, Ruben Martins, Stephan Gocht, Jakob
 * Nordstrom
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

#include "Encodings.h"
#include "UAdder.h"
#include "UGTE.h"
#include "USequential.h"
#include "UTotalizer.h"
#include "VAdder.h"
#include "VGTE.h"
#include "VSequential.h"
#include "VTotalizer.h"

using namespace openwbo;

void Encodings::encode(Card *card, MaxSATFormula *maxsat_formula) {

  if (_cardinality_type == _CARD_SEQUENTIAL_) {
    USequential *seq = new USequential();
    seq->encode(card, maxsat_formula);
  } else if (_cardinality_type == _CARD_TOTALIZER_) {
    UTotalizer *tot = new UTotalizer();
    tot->encode(card, maxsat_formula);
  } else if (_cardinality_type == _CARD_VSEQUENTIAL_) {
    VSequential *vseq = new VSequential();
    vseq->encode(card, maxsat_formula);
  } else if (_cardinality_type == _CARD_VTOTALIZER_) {
    VTotalizer *tot = new VTotalizer();
    tot->encode(card, maxsat_formula);
  } else
    assert(false);
}

void Encodings::encode(PB *pb, MaxSATFormula *maxsat_formula) {

  if (_pb_type == _PB_GTE_) {
    UGTE *gte = new UGTE();
    gte->encode(pb, maxsat_formula);
  } else if (_pb_type == _PB_ADDER_) {
    UAdder *add = new UAdder();
    add->encode(pb, maxsat_formula);
  } else if (_pb_type == _PB_VGTE_) {
    VGTE *gte = new VGTE();
    gte->encode(pb, maxsat_formula);
  } else if (_pb_type == _PB_VADDER_) {
    VAdder *add = new VAdder();
    add->encode(pb, maxsat_formula);
  } else
    assert(false);
}

void Encodings::addUnitClause(MaxSATFormula *mx, Lit a) {
  assert(clause.size() == 0);
  assert(a != lit_Undef);
  assert(var(a) < mx->nVars());
  clause.push(a);
  mx->incId();
  mx->addHardClause(clause);
  clause.clear();
}

void Encodings::addBinaryClause(MaxSATFormula *mx, Lit a, Lit b) {
  assert(clause.size() == 0);
  assert(a != lit_Undef && b != lit_Undef);
  assert(var(a) < mx->nVars() && var(b) < mx->nVars());
  clause.push(a);
  clause.push(b);
  mx->incId();
  mx->addHardClause(clause);
  clause.clear();
}

void Encodings::addTernaryClause(MaxSATFormula *mx, Lit a, Lit b, Lit c) {
  assert(clause.size() == 0);
  assert(a != lit_Undef && b != lit_Undef && c != lit_Undef);
  assert(var(a) < mx->nVars() && var(b) < mx->nVars() && var(c) < mx->nVars());
  clause.push(a);
  clause.push(b);
  clause.push(c);
  mx->incId();
  mx->addHardClause(clause);
  clause.clear();
}

void Encodings::addQuaternaryClause(MaxSATFormula *mx, Lit a, Lit b, Lit c,
                                    Lit d) {
  assert(clause.size() == 0);
  assert(a != lit_Undef && b != lit_Undef && c != lit_Undef && d != lit_Undef);
  assert(var(a) < mx->nVars() && var(b) < mx->nVars() && var(c) < mx->nVars() &&
         var(d) < mx->nVars());
  clause.push(a);
  clause.push(b);
  clause.push(c);
  clause.push(d);
  mx->incId();
  mx->addHardClause(clause);
  clause.clear();
}

void Encodings::addClause(MaxSATFormula *mx, vec<Lit> &c) {
  mx->incId();
  mx->addHardClause(c);
}

std::pair<PBPred *, PBPred *> Encodings::reify(Lit z, PB *pb) {
  vec<Lit> lits;
  vec<int64_t> coeffs;
  int64_t sum = 0;
  for (int i = 0; i < pb->_lits.size(); i++) {
    lits.push(~pb->_lits[i]);
    coeffs.push(pb->_coeffs[i]);
    sum += pb->_coeffs[i];
  }

  pb->addProduct(~z, pb->_rhs);
  PBPred *pbp_geq = new PBPred(mx->getIncProofLogId(), pb, var(z) + 1, 0);
  mx->addProofExpr(pbp_geq);

  PB *pb_leq = new PB(lits, coeffs, sum - pb->_rhs + 1, _PB_GREATER_OR_EQUAL_);
  pb_leq->addProduct(z, sum - pb->_rhs + 1);
  PBPred *pbp_leq = new PBPred(mx->getIncProofLogId(), pb_leq, var(z) + 1, 1);
  mx->addProofExpr(pbp_leq);

  std::pair<PBPred *, PBPred *> res;
  res.first = pbp_geq;
  res.second = pbp_leq;
  return res;
}

void Encodings::derive_ordering(PBPred *p1, PBPred *p2) {
  int d = 0;
  for (int i = 0; i < p1->_ctr->_coeffs.size(); i++) {
    if (var(p1->_ctr->_lits[i]) + 1 != p1->_v)
      d += p1->_ctr->_coeffs[i];
  }
  PBPp *pbp = new PBPp(mx->getIncProofLogId());
  pbp->addition(p1->_ctrid, p2->_ctrid);
  pbp->division(d);
  mx->addProofExpr(pbp);
}

int Encodings::derive_sum(vec<PBPred *> &sum) {
  if (sum.size() < 2) {
    assert(sum.size() == 1);
    return sum[0]->_ctrid;
  }

  int c = sum[0]->_ctrid;
  for (int j = 2; j <= sum.size(); j++) {
    PBPp *pbp = new PBPp(mx->getIncProofLogId());
    // avoid multiplication by 1
    if (j - 1 == 1)
      pbp->addition(c, sum[j - 1]->_ctrid);
    else {
      pbp->multiplication(c, j - 1);
      pbp->addition(sum[j - 1]->_ctrid);
    }
    pbp->division(j);
    mx->addProofExpr(pbp);

    // not needed but may make the proof easier to read
    if (j != sum.size())
      c = -1;
    else
      c = pbp->_ctrid;
  }
  return c;
}

std::pair<int, int> Encodings::derive_unary_sum(vec<Lit> &left, vec<Lit> &right,
                                                int rhs) {
  vec<PBPred *> sum_leq;
  vec<PBPred *> sum_geq;

  for (int j = 0; j < right.size(); j++) {
    // introduce variables as reification
    // reify(z_j <-> sum^n_i l_i >= j)
    vec<int64_t> coeffs;
    coeffs.growTo(left.size(), 1);
    PB *pb = new PB(left, coeffs, j + 1, _PB_GREATER_OR_EQUAL_);
    std::pair<PBPred *, PBPred *> p = reify(right[j], pb);
    sum_geq.push(p.first);
    sum_leq.push(p.second);
  }

  // reverse sum_leq
  vec<PBPred *> sum_leq_rev;
  for (int i = sum_leq.size() - 1; i >= 0; i--) {
    sum_leq_rev.push(sum_leq[i]);
  }

  int c_geq = derive_sum(sum_geq);
  int c_leq = derive_sum(sum_leq_rev);

  for (int i = 0; i < right.size() - 1; i++) {
    if (i + 1 < sum_geq.size()) {
      derive_ordering(sum_leq[i], sum_geq[i + 1]);
    }
  }

  std::pair<int, int> res;
  res.first = c_geq;
  res.second = c_leq;

  return res;
}
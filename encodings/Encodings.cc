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
    assert(false);
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
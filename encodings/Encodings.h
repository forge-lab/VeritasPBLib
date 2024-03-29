/*!
 * \author Ruben Martins - rubenm@andrew.cmu.edu
 *
 * @section LICENSE
 *
 * VeritasPBLib, Copyright (c) 2021-2022, Stephan Gocht, Andy Oertel
 *                                        Ruben Martins, Jakob Nordstrom
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

#ifndef Encodings_h
#define Encodings_h

#include "core/Solver.h"

#include "../MaxSATFormula.h"
#include "../MaxTypes.h"
#include "core/SolverTypes.h"

using NSPACE::Lit;
using NSPACE::lit_Error;
using NSPACE::lit_Undef;
using NSPACE::mkLit;
using NSPACE::Solver;
using NSPACE::vec;

namespace openwbo {

//=================================================================================================
class Encodings {

public:
  Encodings(pb_Cardinality cardinality_type = _CARD_SEQUENTIAL_,
            pb_PB pb_type = _PB_ADDER_) {
    _cardinality_type = cardinality_type;
    _pb_type = pb_type;
  }
  ~Encodings() {}

  // Auxiliary methods for creating clauses
  //
  void addUnitClause(MaxSATFormula *mx, Constraint *ctr, Lit a);
  void addBinaryClause(MaxSATFormula *mx, Constraint *ctr, Lit a, Lit b);
  void addTernaryClause(MaxSATFormula *mx, Constraint *ctr, Lit a, Lit b,
                        Lit c);
  void addQuaternaryClause(MaxSATFormula *mx, Constraint *ctr, Lit a, Lit b,
                           Lit c, Lit d);
  void addClause(MaxSATFormula *mx, Constraint *ctr, vec<Lit> &c);
  void encode(Card *card, MaxSATFormula *maxsat_formula, bool proof = true);
  void encode(PB *pb, MaxSATFormula *maxsat_formula, bool proof = true);

protected:
  vec<Lit> clause; // Temporary clause to be used while building the encodings.
  pb_Cardinality _cardinality_type;
  pb_PB _pb_type;

  // Auxillary methods for proof logging
  MaxSATFormula *mx;
  std::pair<PBPred *, PBPred *> reify(Constraint *ctr, Lit z, PB *pb);
  void derive_ordering(Constraint *ctr, PBPred *p1, PBPred *p2);
  int derive_sum(Constraint *ctr, vec<PBPred *> &sum);
  std::pair<int, int> derive_unary_sum(Constraint *ctr, vec<Lit> &left,
                                       vec<Lit> &right);
};
} // namespace openwbo

#endif

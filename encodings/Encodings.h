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

#ifndef Encodings_h
#define Encodings_h

#ifdef SIMP
#include "simp/SimpSolver.h"
#else
#include "core/Solver.h"
#endif

#include "../MaxTypes.h"
#include "core/SolverTypes.h"
#include "../MaxSATFormula.h"

using NSPACE::vec;
using NSPACE::Lit;
using NSPACE::mkLit;
using NSPACE::lit_Error;
using NSPACE::lit_Undef;
using NSPACE::Solver;

namespace openwbo {

//=================================================================================================
class Encodings {

public:
  Encodings(cardinality cardinality_type = _CARD_SEQUENTIAL_) {
    _cardinality_type = cardinality_type;
  }
  ~Encodings() {}

  // Auxiliary methods for creating clauses
  //
  void addUnitClause(MaxSATFormula * mx, Lit a);
  void addBinaryClause(MaxSATFormula * mx, Lit a, Lit b);
  void addTernaryClause(MaxSATFormula * mx, Lit a, Lit b, Lit c);
  void addQuaternaryClause(MaxSATFormula * mx, Lit a, Lit b, Lit c, Lit d);
  void encode(Card *card, MaxSATFormula *maxsat_formula);

protected:
  vec<Lit> clause; // Temporary clause to be used while building the encodings.
  cardinality _cardinality_type;
  
};
} // namespace openwbo

#endif

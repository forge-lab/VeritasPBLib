/*!
 * \author Andy Oertel - andy.oertel@cs.lth.se
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

#ifndef VTotalizer_h
#define VTotalizer_h

#include "core/Solver.h"

#include "Encodings.h"
#include "core/SolverTypes.h"

namespace openwbo {

class VTotalizer : public Encodings {

public:
  VTotalizer(bool proof = true) {
    _proof = proof;
  }
  ~VTotalizer() {}

  void encode(Card *card, MaxSATFormula *maxsat_formula);

private:
  void encode(Card *card, MaxSATFormula *maxsat_formula, pb_Sign sign);
  void adder(MaxSATFormula *maxsat_formula, Card *card, vec<Lit> &left,
             vec<Lit> &right, vec<Lit> &output);
  void toCNF(MaxSATFormula *maxsat_formula, Card *card, vec<Lit> &lits,
             int64_t k, vec<int> &geq, vec<int> &leq);
  int _rhs;
  vec<Lit> cardinality_inlits; // Stores the inputs of the cardinality
                               // constraint encoding for the totalizer encoding
  vec<Lit> cardinality_outlits; // Stores the outputs of the cardinality
                                // constraint encoding for incremental solving

  bool _proof;
};
} // namespace openwbo

#endif

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

#ifndef VSequential_h
#define VSequential_h

#include "core/Solver.h"

#include "Encodings.h"
#include "core/SolverTypes.h"
#include "../FormulaVeriPB.h"

namespace openwbo {

class VSequential : public Encodings {

public:
  VSequential() {
  }
  ~VSequential() {}

  void encode(Card *card, MaxSATFormula *maxsat_formula);

private:
  void encode(Card *card, MaxSATFormula *maxsat_formula, pb_Sign sign);
  std::pair<int,int> derive_unary_sum(vec<Lit>& left, vec<Lit>& right, int rhs);
  std::pair<PBPred*,PBPred*> reify(Lit z, PB * pb);
  int derive_sum(vec<PBPred*>& sum);
  void derive_ordering(PBPred* p1, PBPred* p2);

  MaxSATFormula *mx;
  
};
} // namespace openwbo

#endif

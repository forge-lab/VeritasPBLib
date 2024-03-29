/*!
 * \author Ruben Martins - rubenm@andrew.cmu.edu
 *
 * @section LICENSE
 *
 * VeritasPBLib, Copyright (c) 2021, Ruben Martins, Stephan Gocht, Jakob
 * Nordstrom PBLib,    Copyright (c) 2012-2013  Peter Steinke
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

#ifndef UAdder_h
#define UAdder_h

#include "core/Solver.h"

#include "Encodings.h"
#include "core/SolverTypes.h"
#include <map>
#include <queue>
#include <utility>
#include <vector>

namespace openwbo {
class UAdder : public Encodings {

public:
  UAdder() {}
  ~UAdder() {}

  void encode(PB *pb, MaxSATFormula *maxsat_formula);

protected:
  vec<Lit> _output;
  vec<Lit> clause;
  std::vector<std::queue<Lit>> _buckets;

  // Encode constraint.
  void encode(PB *pb, MaxSATFormula *maxsat_formula, pb_Sign current_sign);

  void FA_extra(MaxSATFormula *maxsat_formula, PB *pb, Lit xc, Lit xs, Lit a,
                Lit b, Lit c);
  Lit FA_carry(MaxSATFormula *maxsat_formula, PB *pb, Lit a, Lit b, Lit c);
  Lit FA_sum(MaxSATFormula *maxsat_formula, PB *pb, Lit a, Lit b, Lit c);
  Lit HA_carry(MaxSATFormula *maxsat_formula, PB *pb, Lit a, Lit b);
  Lit HA_sum(MaxSATFormula *maxsat_formula, PB *pb, Lit a, Lit b);
  void adderTree(MaxSATFormula *maxsat_formula, PB *pb,
                 std::vector<std::queue<Lit>> &buckets, vec<Lit> &result,
                 uint64_t log_k);
  void lessThanOrEqual(MaxSATFormula *maxsat_formula, PB *pb, vec<Lit> &xs,
                       std::vector<uint64_t> &ys);
  void greaterThanOrEqual(MaxSATFormula *maxsat_formula, PB *pb, vec<Lit> &xs,
                          std::vector<uint64_t> &ys);
  void numToBits(std::vector<uint64_t> &bits, uint64_t n, uint64_t number);
  uint64_t ld64(const uint64_t x);
};
} // namespace openwbo

#endif

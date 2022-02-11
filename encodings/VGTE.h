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

#ifndef VGTE_h
#define VGTE_h

#include "core/Solver.h"

#include "Encodings.h"
#include "UGTE.h"
#include "core/SolverTypes.h"
#include <map>
#include <utility>
#include <vector>

namespace openwbo {
class VGTE : public Encodings {

public:
  VGTE() { current_pb_rhs = 0; }
  ~VGTE() {}

  // Encode constraint.
  void encode(PB *pb, MaxSATFormula *maxsat_formula);

protected:
  void encode(PB *pb, MaxSATFormula *maxsat_formula, pb_Sign current_sign);
  void encode(MaxSATFormula *maxsat_formula, PB *pb, vec<Lit> &lits,
              vec<uint64_t> &coeffs, uint64_t rhs, pb_Sign current_sign,
              bool flipped);

  bool encodeLeq(uint64_t k, MaxSATFormula *maxsat_formula, PB *pb,
                 const weightedlitst &iliterals, wlit_mapt &oliterals,
                 pb_Sign current_sign, vec<int> &geq, vec<int> &leq);
  Lit getNewLit(MaxSATFormula *maxsat_formula);
  Lit get_var(MaxSATFormula *maxsat_formula, wlit_mapt &oliterals,
              uint64_t weight);
  uint64_t succ(wlit_mapt &literals, uint64_t weight);

  vec<Lit> pb_outlits; // Stores the outputs of the pseudo-Boolean constraint
                       // encoding for incremental solving.
  uint64_t current_pb_rhs; // Stores the current value of the rhs of the
                           // pseudo-Boolean constraint.

  // Stores unit lits. Used for lits that have a coeff larger than rhs.
  wlit_mapt pb_oliterals;
  vec<Lit> unit_lits;
  vec<uint64_t> unit_coeffs;

  // proof logging (left...A, right...B, current...E)
  std::pair<int, int> derive_sparse_unary_sum(MaxSATFormula *maxsat_formula,
                                              PB *pb, wlit_mapt &left,
                                              wlit_mapt &right,
                                              wlit_mapt &current);
  weightedlitst sort_to_list(wlit_mapt &map);
  void try_all_values(PB *pb, weightedlitst &left, weightedlitst &right,
                      Lit &z_eq);
};

} // namespace openwbo

#endif

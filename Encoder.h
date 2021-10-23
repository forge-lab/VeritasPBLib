
/*!
 * \author Ruben Martins - ruben@sat.inesc-id.pt
 *
 * @section LICENSE
 *
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

#ifndef Encoder_h
#define Encoder_h

#ifdef SIMP
#include "simp/SimpSolver.h"
#else
#include "core/Solver.h"
#endif

#include "MaxTypes.h"
#include "core/SolverTypes.h"

// Encodings
#include "encodings/Enc_Sequential.h"
#include "MaxSATFormula.h"

using NSPACE::vec;
using NSPACE::Lit;
using NSPACE::Solver;

namespace openwbo {

//=================================================================================================
class Encoder {

public:
  Encoder(int cardinality = _CARD_SEQUENTIAL_, int pb = _PB_SWC_) {
    pb_encoding = pb;
    cardinality_encoding = cardinality;
  }

  ~Encoder() {}

  // TEMP
  vec<Lit> &lits();
  vec<Lit> &outputs();

  // Cardinality encodings:
  //
  // Encode cardinality constraint into CNF.
  void encodeCardinality(Card *card, MaxSATFormula *maxsat_formula);

  // PB encodings:
  //
  // Encode pseudo-Boolean constraint into CNF.
  void encodePB(MaxSATFormula *mx, vec<Lit> &lits, vec<uint64_t> &coeffs, uint64_t rhs);
  
  // Controls the type of encoding to be used:
  //
  void setCardEncoding(int enc) { cardinality_encoding = enc; }
  int getCardEncoding() { return cardinality_encoding; }

  void setPBEncoding(int enc) { pb_encoding = enc; }
  int getPBEncoding() { return pb_encoding; }

protected:
  int cardinality_encoding;
  int pb_encoding;
  int amo_encoding;

  // Cardinality encodings
  Sequential sequential;

};
} // namespace openwbo

#endif


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

#ifndef Encoder_h
#define Encoder_h

#include "core/Solver.h"

#include "MaxTypes.h"
#include "core/SolverTypes.h"

// Encodings
#include "encodings/USequential.h"
#include "encodings/UTotalizer.h"
#include "encodings/UAdder.h"
#include "encodings/VSequential.h"
#include "MaxSATFormula.h"

using NSPACE::vec;
using NSPACE::Lit;
using NSPACE::Solver;

namespace openwbo {

//=================================================================================================
class Encoder {

public:
  Encoder(int cardinality = _CARD_SEQUENTIAL_, int pb = _PB_ADDER_) {
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
  void encodePB(PB *pb, MaxSATFormula *mx);
  
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
  USequential sequential;
  UTotalizer totalizer;
  VSequential vsequential;

  // PB encodings
  UAdder adder;

};
} // namespace openwbo

#endif

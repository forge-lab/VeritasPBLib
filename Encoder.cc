/*!
 * \author Ruben Martins - ruben@sat.inesc-id.pt
 *
 * @section LICENSE
 *
 * Open-WBO, Copyright (c) 2013-2018, Ruben Martins, Vasco Manquinho, Ines Lynce
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

#include "Encoder.h"

using namespace openwbo;


/************************************************************************************************
 //
 // Encoding of cardinality constraints
 //
 ************************************************************************************************/
//
// Manages the encoding of cardinality encodings.
void Encoder::encodeCardinality(Card *card, MaxSATFormula *maxsat_formula) {

  switch (cardinality_encoding) {
  case _CARD_SEQUENTIAL_:
    sequential.encode(card, maxsat_formula);
    break;

  case _CARD_VSEQUENTIAL_:
    vsequential.encode(card, maxsat_formula);
    break;

  default:
    printf("c Error: Invalid cardinality encoding.\n");
    printf("s UNKNOWN\n");
    exit(_ERROR_);
  }
}

/************************************************************************************************
 //
 // Encoding of pseudo-Boolean constraints
 //
 ************************************************************************************************/
//
// Manages the encoding of PB encodings.
void Encoder::encodePB(PB *pb, MaxSATFormula *mx) {

  switch (pb_encoding) {
    case _PB_ADDER_:
      adder.encode(pb, mx);
      break;
  
  default:
    printf("c Error: Invalid PB encoding.\n");
    printf("s UNKNOWN\n");
    exit(_ERROR_);
  }
}


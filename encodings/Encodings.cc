/*!
 * \author Ruben Martins - rubenm@andrew.cmu.edu
 *
 * @section LICENSE
 *
 * VeritasPBLib, Copyright (c) 2021, Ruben Martins, Stephan Gocht, Jakob Nordstrom
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
#include "USequential.h"
#include "UTotalizer.h"
#include "UAdder.h"

using namespace openwbo;

void Encodings::encode(Card *card, MaxSATFormula *maxsat_formula){

  if( _cardinality_type == _CARD_SEQUENTIAL_){ 
    USequential * seq = new USequential();
    seq->encode(card, maxsat_formula);
  } else if (_cardinality_type == _CARD_TOTALIZER_){
    UTotalizer * tot = new UTotalizer();
    tot->encode(card, maxsat_formula);
  } else if (_cardinality_type == _CARD_ADDER_){
    assert(false);
  } else assert(false);
}

void Encodings::encode(PB *pb, MaxSATFormula *maxsat_formula){

  if( _pb_type == _PB_SWC_){ 
    assert(false);
  } else if (_pb_type == _PB_GTE_){
    assert(false);
  } else if (_pb_type == _PB_ADDER_){
    UAdder * add = new UAdder();
    add->encode(pb, maxsat_formula);
  } else assert(false);
}

void Encodings::addUnitClause(MaxSATFormula * mx, Lit a) {
  assert(clause.size() == 0);
  assert(a != lit_Undef);
  assert(var(a) < mx->nVars());
  clause.push(a);
  mx->incId();
  mx->addHardClause(clause);
  clause.clear();
}

void Encodings::addBinaryClause(MaxSATFormula * mx, Lit a, Lit b) {
  assert(clause.size() == 0);
  assert(a != lit_Undef && b != lit_Undef);
  assert(var(a) < mx->nVars() && var(b) < mx->nVars());
  clause.push(a);
  clause.push(b);
  mx->incId();
  mx->addHardClause(clause);
  clause.clear();
}

void Encodings::addTernaryClause(MaxSATFormula * mx, Lit a, Lit b, Lit c) {
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

void Encodings::addQuaternaryClause(MaxSATFormula * mx, Lit a, Lit b, Lit c, Lit d) {
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

void Encodings::addClause(MaxSATFormula *mx, vec<Lit>& c){
  mx->incId();
  mx->addHardClause(c);
}

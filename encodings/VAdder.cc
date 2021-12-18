/*!
 * \author Ruben Martins - rubenm@andrew.cmu.edu
 *
 * @section LICENSE
 *
 * VeritasPBLib, Copyright (c) 2021, Ruben Martins, Stephan Gocht, Jakob Nordstrom
 * PBLib,    Copyright (c) 2012-2013  Peter Steinke
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

#include "VAdder.h"
#include <algorithm>
#include <numeric>

using namespace openwbo;

void VAdder::FA_extra (MaxSATFormula *maxsat_formula, Lit xc, Lit xs, Lit a, Lit b, Lit c )
{
  
  clause.clear();
  addTernaryClause(maxsat_formula, ~xc, ~xs, a);
  addTernaryClause(maxsat_formula, ~xc, ~xs, b);
  addTernaryClause(maxsat_formula, ~xc, ~xs, c);

  addTernaryClause(maxsat_formula, xc, xs, ~a);
  addTernaryClause(maxsat_formula, xc, xs, ~b);
  addTernaryClause(maxsat_formula, xc, xs, ~c);
}


Lit VAdder::FA_carry (MaxSATFormula *maxsat_formula, Lit a, Lit b, Lit c ) {
  
  Lit x = mkLit(maxsat_formula->nVars(), false);
  maxsat_formula->newVar();

  addTernaryClause(maxsat_formula, b, c, ~x);
  addTernaryClause(maxsat_formula, a, c, ~x);
  addTernaryClause(maxsat_formula, a, b, ~x);

  addTernaryClause(maxsat_formula, ~b, ~c, x);
  addTernaryClause(maxsat_formula, ~a, ~c, x);
  addTernaryClause(maxsat_formula, ~a, ~b, x);

  return x;
}

Lit VAdder::FA_sum (MaxSATFormula *maxsat_formula, Lit a, Lit b, Lit c )
{
    Lit x = mkLit(maxsat_formula->nVars(), false);
    maxsat_formula->newVar();

    addQuaternaryClause(maxsat_formula, a, b, c, ~x);
    addQuaternaryClause(maxsat_formula, a, ~b, ~c, ~x);
    addQuaternaryClause(maxsat_formula, ~a, b, ~c, ~x);
    addQuaternaryClause(maxsat_formula, ~a, ~b, c, ~x);

    addQuaternaryClause(maxsat_formula, ~a, ~b, ~c, x);
    addQuaternaryClause(maxsat_formula, ~a, b, c, x);
    addQuaternaryClause(maxsat_formula, a, ~b, c, x);
    addQuaternaryClause(maxsat_formula, a, b, ~c, x);

    return x;
}

Lit VAdder::HA_carry (MaxSATFormula *maxsat_formula, Lit a, Lit b) // a AND b
{  
  Lit x = mkLit(maxsat_formula->nVars(), false);
  maxsat_formula->newVar();

  addBinaryClause(maxsat_formula, a, ~x);
  addBinaryClause(maxsat_formula, b, ~x);
  addTernaryClause(maxsat_formula, ~a, ~b, x);

  return x;
}

Lit VAdder::HA_sum (MaxSATFormula *maxsat_formula, Lit a, Lit b ) // a XOR b
{
  Lit x = mkLit(maxsat_formula->nVars(), false);
  maxsat_formula->newVar();

  addTernaryClause(maxsat_formula, ~a, ~b, ~x);
  addTernaryClause(maxsat_formula, a, b, ~x);
  
  addTernaryClause(maxsat_formula, ~a, b, x);
  addTernaryClause(maxsat_formula, a, ~b, x);

  return x;
}


void VAdder::adderTree (MaxSATFormula *maxsat_formula, std::vector< std::queue< Lit > > & buckets, vec< Lit >& result ) {
  Lit x,y,z;
  Lit u = lit_Undef;

  for ( size_t i = 0; i < buckets.size(); i++ ) {
      if ( buckets[i].size() == 0 )
    continue;

      if ( i == buckets.size() - 1 && buckets[i].size() >= 2 ) {
    buckets.push_back ( std::queue<Lit>() );
    result.push ( u );
    }

      while ( buckets[i].size() >= 3 ) {
    x = buckets[i].front();
    buckets[i].pop();
    y = buckets[i].front();
    buckets[i].pop();
    z = buckets[i].front();
    buckets[i].pop();
    Lit xs = FA_sum ( maxsat_formula, x,y,z );
    Lit xc = FA_carry ( maxsat_formula, x,y,z );
    buckets[i  ].push ( xs );
    buckets[i+1].push ( xc );
    FA_extra(maxsat_formula, xc, xs, x, y, z);
    }

      if ( buckets[i].size() == 2 ) {
    x = buckets[i].front();
    buckets[i].pop();
    y = buckets[i].front();
    buckets[i].pop();
    buckets[i  ].push ( HA_sum ( maxsat_formula, x,y ) );
    buckets[i+1].push ( HA_carry ( maxsat_formula, x,y ) );
    }


      result[i] = buckets[i].front();
      buckets[i].pop();
      }

  }

// Generates clauses for “xs <= ys”, assuming ys has only constant signals (0 or 1).
// xs and ys must have the same size

void VAdder::lessThanOrEqual (MaxSATFormula *maxsat_formula, vec< Lit > & xs, std::vector< uint64_t > & ys) {
  assert ( (size_t)xs.size() == ys.size() );
  vec<Lit> clause;
  bool skip;
  for ( int i = 0; i < xs.size(); ++i ) {
      if ( ys[i] == 1 || xs[i] == lit_Undef )
    continue;
      
      clause.clear();

      skip = false;

      for ( int j = i + 1; j < xs.size(); ++j )
      {
    if ( ys[j] == 1 )
    {
        if ( xs[j] == lit_Undef )
        {
      skip = true;
      break;
        }

        clause.push ( ~xs[j] );
    }
    else
    {
        assert ( ys[j] == 0 );

        if ( xs[j] == lit_Undef )
      continue;

        clause.push ( xs[j] );
    }
      }

      if ( skip )
    continue;

      clause.push ( ~xs[i] );

      addClause(maxsat_formula, clause);
      }

}


void VAdder::numToBits ( std::vector<uint64_t> & bits, uint64_t n, uint64_t number ) {
    bits.clear();

  
  for ( int64_t i = n - 1; i >= 0; --i ) {
      uint64_t tmp = ((uint64_t)1) << i;
      if ( number < tmp ) {
    bits.push_back ( 0 );
    }
      else {
    bits.push_back ( 1 );
    number -= tmp;
    }
      }

  reverse ( bits.begin(), bits.end() );
}

void VAdder::encode(PB *pb, MaxSATFormula *maxsat_formula){

    switch (pb->_sign){
      case _PB_EQUAL_:
        encode(pb, maxsat_formula, _PB_GREATER_OR_EQUAL_);
        encode(pb, maxsat_formula, _PB_LESS_OR_EQUAL_);
        break;
      case _PB_LESS_OR_EQUAL_:
        encode(pb, maxsat_formula, _PB_LESS_OR_EQUAL_);
        break;
      case _PB_GREATER_OR_EQUAL_:
        encode(pb, maxsat_formula, _PB_GREATER_OR_EQUAL_);
        break;
      default:
        assert(false);
    }

}

void VAdder::encode(PB *pb, MaxSATFormula *maxsat_formula, pb_Sign sign){
  assert (sign != _PB_EQUAL_);

  vec<Lit> lits;
  vec<uint64_t> coeffs;
  
  pb->_lits.copyTo(lits);
  for (int i = 0; i < pb->_coeffs.size(); i++){
    assert (pb->_coeffs[i] > 0);
    coeffs.push(pb->_coeffs[i]);
  }
  uint64_t rhs = pb->_rhs;


  // transform it into <=
  if (sign == _PB_GREATER_OR_EQUAL_){
    int s = 0;
      for (int i = 0; i < coeffs.size(); i++) {
        s += coeffs[i];
        lits[i] = ~(lits[i]);
      }
      rhs = s - rhs;
  }


  // TODO: should we simplify the PB constraint?

  encode(maxsat_formula, lits, coeffs, rhs);

}


void VAdder::encode(MaxSATFormula *maxsat_formula, vec<Lit> &lits, vec<uint64_t> &coeffs, uint64_t rhs){

    _output.clear();

    uint64_t nb = ld64(rhs); // number of bits
    Lit u = lit_Undef;

    for ( uint64_t iBit = 0; iBit < nb; ++iBit ) {
        _buckets.push_back ( std::queue<Lit>() );
        _output.push ( u );
        for ( int iVar = 0; iVar < lits.size(); ++iVar ) {
            if ( ( ( ((int64_t)1) << iBit ) & coeffs[iVar] ) != 0 )
                _buckets.back().push ( lits[iVar] );
            }
        }

    std::vector<uint64_t> kBits;

    adderTree (maxsat_formula, _buckets, _output);
  
    numToBits (kBits, _buckets.size(), rhs );

    lessThanOrEqual (maxsat_formula, _output, kBits);
}

uint64_t VAdder::ld64(const uint64_t x)
{
  return (sizeof(uint64_t) << 3) - __builtin_clzll (x);
//   cout << "x " << x << endl;
//   int ldretutn = 0;
//   for (int i = 0; i < 63; ++i)
//   {
//     if ((x & (1 << i)) > 0)
//     {
//       cout << "ldretutn " << ldretutn << endl;
//       ldretutn = i + 1;
//     }
//   }
//   
//   return ldretutn;
}













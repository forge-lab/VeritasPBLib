/*!
 * \author Vasco Manquinho - vmm@sat.inesc-id.pt
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

#ifndef FormulaPB_h
#define FormulaPB_h

#ifdef SIMP
#include "simp/SimpSolver.h"
#else
#include "core/Solver.h"
#endif

#include "MaxTypes.h"

using NSPACE::vec;
using NSPACE::Lit;

namespace openwbo {

// Cardinality constraint of the form atMostK
class Card {

public:
  Card(vec<Lit> &lits, int64_t rhs, pb_Sign sign = _PB_LESS_OR_EQUAL_, uint id = 0) {
    lits.copyTo(_lits);
    _rhs = rhs;
    _sign = sign;
    _id = id;
    // if (sign) {
    //   int s = 0;
    //   for (int i = 0; i < _lits.size(); i++) {
    //     s += 1;
    //     _lits[i] = ~_lits[i];
    //   }
    //   _rhs = s - _rhs;
    // }
  }

  Card() { _rhs = 0; }
  ~Card() {}

  void print() {
    printf("* Card[%d]: ",_id);

    for (int i = 0; i < _lits.size(); i++) {
      if (sign(_lits[i]))
        printf("~");
      printf("%d ", var(_lits[i]) + 1);
    }
    if (_sign == _PB_EQUAL_)
      printf(" = %d\n", (int)_rhs);
    else if (_sign == _PB_GREATER_OR_EQUAL_)
      printf(" >= %d\n", (int)_rhs);
    else if (_sign == _PB_LESS_OR_EQUAL_)
      printf(" <= %d\n", (int)_rhs);
    else assert(false);
 }

  vec<Lit> _lits;
  int64_t _rhs;
  pb_Sign _sign;
  uint _id;
};

// PB constraint. The constraint sign is encoded in the structure.
class PB {

public:
  PB(vec<Lit> &lits, vec<int64_t> &coeffs, int64_t rhs, pb_Sign s = _PB_LESS_OR_EQUAL_) {
    lits.copyTo(_lits);
    coeffs.copyTo(_coeffs);
    _rhs = rhs;
    _sign = s;
  }

  PB() {
    _rhs = 0;
    _sign = _PB_LESS_OR_EQUAL_;
  }
  ~PB() {}

  void addProduct(Lit l, int64_t c) {
    _coeffs.push();
    _lits.push();
    if (c >= 0) {
      _coeffs[_coeffs.size() - 1] = c;
      _lits[_lits.size() - 1] = l;
    } else {
      _coeffs[_coeffs.size() - 1] = -c;
      _lits[_lits.size() - 1] = ~l;
      _rhs += -c;
    }
  }

  void addRHS(int64_t rhs) { _rhs += rhs; }

  // void changeSign() {
  //   int s = 0;
  //   for (int i = 0; i < _coeffs.size(); i++) {
  //     s += _coeffs[i];
  //     _lits[i] = ~(_lits[i]);
  //   }
  //   _rhs = s - _rhs;
  //   _sign = !(_sign);
  // }

  bool isClause() {
    // unit clauses
    if (_sign == _PB_EQUAL_){
      if (_coeffs.size() != 1) return false;
    } else if (_sign == _PB_GREATER_OR_EQUAL_){
      int rhs = 1;
      for (int i = 0; i < _coeffs.size(); i++){
        if (_coeffs[i] != 1 && _coeffs[i] != -1) return false;
        if (_coeffs[i] == -1) rhs--;
      }
      if (rhs != _rhs) return false;        
    } else if (_sign == _PB_LESS_OR_EQUAL_){
      // TODO: support <= for clause detection
      printf("c Error: PB constraint should be normalized to only include = and >=.\n");
      printf("s UNKNOWN\n");
      exit(_ERROR_);
    }

    // Assume _sign == false...
    // bool sign = _sign;
    // if (_sign)
    //   changeSign();
    // if (_rhs != 1) {
    //   if (_sign != sign)
    //     changeSign();
    //   return false;
    // }
    // for (int i = 0; i < _coeffs.size(); i++) {
    //   if (_coeffs[i] != 1) {
    //     if (_sign != sign)
    //       changeSign();
    //     return false;
    //   }
    // }
    return true;
  }

  bool isCardinality() {
    // // Assume _sign == false...
    // bool sign = _sign;
    // if (_sign)
    //   changeSign();
    for (int i = 0; i < _coeffs.size(); i++) {
      if (_coeffs[i] != 1) {
        return false;
      }
    }
    return true;
  }

  std::string print() {
    std::stringstream ss;
    for (int i = 0; i < _coeffs.size(); i++) {
      ss << _coeffs[i] << " ";
      if (sign(_lits[i]))
        ss << "~";
      ss << "x" << var(_lits[i]) + 1 << " ";
    }
    if (_sign == _PB_EQUAL_) ss << "= ";
    else if (_sign == _PB_LESS_OR_EQUAL_) ss << "<= ";
    else if (_sign == _PB_GREATER_OR_EQUAL_) ss << ">= ";
    ss <<  _rhs << " ;";
    return ss.str();
  }

  vec<int64_t> _coeffs;
  vec<Lit> _lits;
  int64_t _rhs;
  pb_Sign _sign;
};

class PBObjFunction {

public:
  PBObjFunction(vec<Lit> &lits, vec<int64_t> &coeffs, int64_t c = 0) {
    lits.copyTo(_lits);
    coeffs.copyTo(_coeffs);
    _const = c;
  }

  PBObjFunction() { _const = 0; }
  ~PBObjFunction() {}

  void addProduct(Lit l, int64_t c) {
    _coeffs.push();
    _lits.push();
    if (c >= 0) {
      _coeffs[_coeffs.size() - 1] = c;
      _lits[_lits.size() - 1] = l;
    } else {
      _coeffs[_coeffs.size() - 1] = -c;
      _lits[_coeffs.size() - 1] = ~l;
      _const += c;
    }
  }

  vec<int64_t> _coeffs;
  vec<Lit> _lits;
  int64_t _const;
};

} // namespace openwbo

#endif

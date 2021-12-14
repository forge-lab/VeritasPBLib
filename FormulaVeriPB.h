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

#ifndef FormulaVeriPB_h
#define FormulaVeriPB_h

#include "core/Solver.h"

#include "MaxTypes.h"
#include "FormulaPB.h"

using NSPACE::vec;
using NSPACE::Lit;
using NSPACE::Var;

namespace openwbo {

class PBP {
  public:
   PBP(){}
   ~PBP(){}

   virtual std::string print() = 0;

};

// used for the definition of the auxiliary variables
class PBPred : public PBP {
  public:
   PBPred(PB * ctr, int v, int value){
    _ctr = ctr;
    _v = v;
    _value = value;
   }
   PBPred(){}
   ~PBPred(){}

    std::string print(){
      std::string wit = " x" + std::to_string(_v) + " -> " + std::to_string(_value);
      std::string s = "red " + _ctr->print() + wit;
      return s;
    }

  PB * _ctr;
  int _v;
  int _value;
};

// this is only useful for debugging and not required for the proof
class PBPe : public PBP {
  public: 
    PBPe(int id, PB * ctr){
      _id = id;
      _ctr = ctr;
    }

    std::string print(){
      std::string s = "e " + std::to_string(_id) + " " + _ctr->print();
      return s;
    }

    PB * _ctr;
    int _id;
};

class PBPp : public PBP {
public:
  PBPp(){
    _p = "p";
  }

  // TODO: worth it to make this more generic?
  // no error handling is currently enforced
  void addition(int c1, int c2){
    _p += " " + std::to_string(c1) + " " + std::to_string(c2) + " +";
  }

  void multiplication(int c1, int factor){
    assert(factor > 0);
    _p += " " + std::to_string(c1) + " " + std::to_string(factor) + " *"; 
  }

  void division(int c1, int divisor){
    assert(divisor > 0);
   _p += " " + std::to_string(c1) + " " + std::to_string(divisor) + " d";  
  }

  void saturation(int c1){
   _p += " " + std::to_string(c1) + " s";  
  }

  // TODO: support literal axioms and weakening
  
  std::string print(){
    return _p;
  }

  std::string _p;

};

// this will be automatically translated from the CNF encoding and do not need to be added
class PBPu : public PBP {
  public:
    PBPu(vec<Lit> clause){
      clause.copyTo(_clause);
    }

    std::string print(){
      std::stringstream ss;
      ss << "u ";
      int rhs = 1;
      for (int i = 0; i < _clause.size(); i++){
        if (sign(_clause[i])){
          ss << "1 ~" << (var(_clause[i])+1);
          rhs--;
        } else ss << "1 " << (var(_clause[i])+1);
      }
      ss << " >= " << rhs << " ;";
      return ss.str();
    }

    vec<Lit> _clause;
};

} // namespace openwbo

#endif

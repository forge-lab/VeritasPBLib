/*!
 * \author Ruben Martins - rubenm@andrew.cmu.edu
 *
 * @section LICENSE
 *
 * Open-WBO, Copyright (c) 2013-2022, Ruben Martins, Vasco Manquinho, Ines Lynce
 * VeritasPBLib, Copyright (c) 2021-2022, Stephan Gocht, Andy Oertel
 *                                        Ruben Martins, Jakob Nordstrom
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

#ifndef MaxSATFormula_h
#define MaxSATFormula_h

#ifdef SIMP
#include "simp/SimpSolver.h"
#else
#include "core/Solver.h"
#endif

#include "FormulaPB.h"
#include "FormulaVeriPB.h"
#include "MaxTypes.h"

#include <fstream>
#include <map>
#include <string>

using NSPACE::Lit;
using NSPACE::lit_Undef;
using NSPACE::mkLit;
using NSPACE::vec;

namespace openwbo {

typedef std::map<std::string, int> nameMap;
typedef std::map<int, std::string> indexMap;
typedef std::map<int, int> varMap;

class Soft {

public:
  /*! The soft class is used to model the soft clauses in a MaxSAT formula. */
  Soft(const vec<Lit> &soft, uint64_t soft_weight, Lit assump_var,
       const vec<Lit> &relax) {
    soft.copyTo(clause);
    weight = soft_weight;
    assumption_var = assump_var;
    relax.copyTo(relaxation_vars);
  }

  Soft() {}
  ~Soft() {
    clause.clear();
    relaxation_vars.clear();
  }

  vec<Lit> clause;    //!< Soft clause
  uint64_t weight;    //!< Weight of the soft clause
  Lit assumption_var; //!< Assumption variable used for retrieving the core
  vec<Lit> relaxation_vars; //!< Relaxation variables that will be added to the
                            //! soft clause
};

class Hard {
  /*! The hard class is used to model the hard clauses in a MaxSAT formula. */
public:
  Hard(const vec<Lit> &hard, uint i = 0) {
    hard.copyTo(clause);
    id = i;
  }

  Hard() {}
  ~Hard() { clause.clear(); }

  void printPBPu(std::stringstream &ss, varMap &v) {
    if (clause.size() == 0) {
      ss << "u >= 1 ;\n";
    } else {
      int rhs = 1;
      ss << "u ";
      for (int i = 0; i < clause.size(); i++) {
        if (sign(clause[i])) {
          ss << "1 ~x";
          // rhs--;
        } else
          ss << "1 x";
        varMap::const_iterator iter = v.find(var(clause[i]));
        if (iter != v.end())
          ss << iter->second << " ";
        else
          ss << (var(clause[i]) + 1) << " ";
      }
      ss << ">= " << rhs << " ;\n";
    }
  }

  std::string printPBPu(varMap &v) {
    std::stringstream ss;
    if (clause.size() == 0) {
      ss << "u >= 1 ;\n";
    } else {
      int rhs = 1;
      ss << "u ";
      for (int i = 0; i < clause.size(); i++) {
        if (sign(clause[i])) {
          ss << "1 ~x";
          // rhs--;
        } else
          ss << "1 x";
        varMap::const_iterator iter = v.find(var(clause[i]));
        if (iter != v.end())
          ss << iter->second << " ";
        else
          ss << (var(clause[i]) + 1) << " ";
      }
      ss << ">= " << rhs << " ;\n";
      return ss.str();
    }
  }

  void print(std::stringstream &ss, varMap &v) {
    if (clause.size() > 0) {
      for (int i = 0; i < clause.size(); i++) {
        if (sign(clause[i]))
          ss << "-";
        varMap::const_iterator iter = v.find(var(clause[i]));
        if (iter != v.end())
          ss << iter->second << " ";
        else
          ss << (var(clause[i]) + 1) << " ";
      }
    }
    ss << "0\n";
  }

  std::string print(varMap &v) {
    std::stringstream ss;
    assert(clause.size() > 0);
    for (int i = 0; i < clause.size(); i++) {
      if (sign(clause[i]))
        ss << "-";
      varMap::const_iterator iter = v.find(var(clause[i]));
      if (iter != v.end())
        ss << iter->second << " ";
      else
        ss << (var(clause[i]) + 1) << " ";
    }
    ss << "0";
    return ss.str();
  }
  vec<Lit> clause; //!< Hard clause
  uint id;         // !< Clause id
};

class MaxSATFormula {
  /*! This class contains the MaxSAT formula and methods for adding soft and
   * hard clauses. */
public:
  MaxSATFormula()
      : hard_weight(UINT64_MAX), problem_type(_UNWEIGHTED_), n_vars(0),
        n_soft(0), n_hard(0), n_initial_vars(0), sum_soft_weight(0),
        max_soft_weight(0) {
    objective_function = NULL;
    format = _FORMAT_MAXSAT_;
    proof_log_id = 0;
  }

  ~MaxSATFormula() {
    for (int i = 0; i < nSoft(); i++) {
      soft_clauses[i].clause.clear();
      soft_clauses[i].relaxation_vars.clear();
    }
    soft_clauses.clear();

    for (int i = 0; i < nHard(); i++)
      hard_clauses[i].clause.clear();
    hard_clauses.clear();
  }

  // old method - not needed at the moment (needs fixing)
  // MaxSATFormula *copyMaxSATFormula();

  /*! Add a new hard clause. */
  void addHardClause(Constraint *ctr, vec<Lit> &lits);

  /*! Add a new soft clause. */
  void addSoftClause(uint64_t weight, vec<Lit> &lits);

  /*! Add a new soft clause with predefined relaxation variables. */
  void addSoftClause(uint64_t weight, vec<Lit> &lits, vec<Lit> &vars);

  int nVars();             // Number of variables.
  int nSoft();             // Number of soft clauses.
  int nHard();             // Number of hard clauses.
  void newVar(int v = -1); // New variable. Set to the given value.

  Lit newLiteral(bool sign = false); // Make a new literal.

  void setProblemType(int type); // Set problem type.
  int getProblemType();          // Get problem type.

  void updateSumWeights(uint64_t weight); // Update initial 'ubCost'.
  uint64_t getSumWeights() { return sum_soft_weight; }

  void setMaximumWeight(uint64_t weight); // Set initial 'currentWeight'.
  uint64_t getMaximumWeight();            // Get 'currentWeight'.

  void setHardWeight(uint64_t weight); // Set initial 'hardWeight'.
  uint64_t getHardWeight() { return hard_weight; }

  /*! Return number of initial variables. */
  int nInitialVars();

  /*! Set initial number of variables. */
  void setInitialVars(int vars);

  /*! Return i-soft clause. */
  Soft &getSoftClause(int pos);

  /*! Return i-hard clause. */
  Hard &getHardClause(int pos);

  /*! Add a new cardinality constraint. */
  void addCardinalityConstraint(Card *card);

  /*! Return number of cardinality constraint. */
  int nCardinalityConstraint() { return cardinality_constraints.size(); }

  /*! Return i-card constraint. */
  Card *getCardinalityConstraint(int pos) {
    return cardinality_constraints[pos];
  }

  /*! Add a new PB constraint. */
  void addPBConstraint(PB *pb);

  /*! Return number of PB constraint. */
  int nPBConstraint() { return pb_constraints.size(); }

  /*! Return i-PB constraint. */
  PB *getPBConstraint(int pos) { return pb_constraints[pos]; }

  int newVarName(char *varName);
  int varID(char *varName);

  void addObjFunction(PBObjFunction *of) {
    objective_function = new PBObjFunction(of->_lits, of->_coeffs, of->_const);
  }

  PBObjFunction *getObjFunction() { return objective_function; }

  int nCard() { return cardinality_constraints.size(); }

  int nPB() { return pb_constraints.size(); }

  int nConstr() {
    return cardinality_constraints.size() + pb_constraints.size();
  }

  void convertPBtoMaxSAT();

  void setFormat(int form) { format = form; }

  int getFormat() { return format; }

  indexMap &getIndexToName() { return _indexToName; }

  varMap &getVarMap() { return _varMap; }

  int getIncProofLogId() {
    proof_log_id++;
    return proof_log_id;
  }

  void bumpIds() { proof_log_id++; }

  void decIds() { proof_log_id--; }

  void bumpProofLogId(int offset) { proof_log_id += offset; }

  void printCNFtoFile(std::string filename);
  void printPBPtoFile(std::string filename);

  PBP *getProofExpr(int i) { return proof_expr[i]; }
  int nProofExpr() { return proof_expr.size(); }
  void addProofExpr(Constraint *ctr, PBP *pbp) {
    ctr->proof_expr_id.push(proof_expr.size());
    proof_expr.push(pbp);
  }

  PBP *getProofClauses(int i) { return proof_cls[i]; }
  int nProofClauses() { return proof_cls.size(); }

protected:
  // MaxSAT database
  //
  vec<Soft> soft_clauses; //<! Stores the soft clauses of the MaxSAT formula.
  vec<Hard> hard_clauses; //<! Stores the hard clauses of the MaxSAT formula.
  vec<int> clause_ids;    //<! Ids of the constraints that are clause.

  vec<PBP *> proof_expr; //<! Stores the proof expressions of the PB conversion
  vec<PBP *> proof_cls;  //<! Stores the proof CNF clauses

  // PB database
  //
  PBObjFunction *objective_function;   //<! Objective function for PB.
  vec<Card *> cardinality_constraints; //<! Stores the cardinality constraints.
  vec<PB *> pb_constraints;            //<! Stores the PB constraints.

  // Properties of the MaxSAT formula
  //
  uint64_t hard_weight; //<! Weight of the hard clauses.
  int problem_type;     //<! Stores the type of the MaxSAT problem.
  int n_vars;           //<! Number of variables used in the SAT solver.
  int n_soft;           //<! Number of soft clauses.
  int n_hard;           //<! Number of hard clauses.
  int n_initial_vars;   //<! Number of variables of the initial MaxSAT formula.
  uint64_t sum_soft_weight; //<! Sum of weights of soft clauses.
  uint64_t max_soft_weight; //<! Maximum weight of soft clauses.

  // Utils for PB formulas
  //
  nameMap _nameToIndex;  //<! Map from variable name to variable id.
  indexMap _indexToName; //<! Map from variable id to variable name.
  varMap _varMap;        //<! Map from variable id in CNF to variable id in PB.

  uint id;           // <! Id for the clauses
  uint proof_log_id; // <! Id used for the constraints in the proof log

  // Format
  //
  int format;
};

} // namespace openwbo

#endif

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

#include <iostream>

#include "MaxSATFormula.h"

using namespace openwbo;

// old method - not needed at the moment (needs fixing)
// MaxSATFormula *MaxSATFormula::copyMaxSATFormula() {
//   assert(format == _FORMAT_MAXSAT_);

//   MaxSATFormula *copymx = new MaxSATFormula();
//   copymx->setInitialVars(nVars());

//   for (int i = 0; i < nVars(); i++)
//     copymx->newVar();

//   for (int i = 0; i < nSoft(); i++)
//     copymx->addSoftClause(getSoftClause(i).weight, getSoftClause(i).clause);

//   for (int i = 0; i < nHard(); i++)
//     copymx->addHardClause(NULL, getHardClause(i).clause);

//   copymx->setProblemType(getProblemType());
//   copymx->updateSumWeights(getSumWeights());
//   copymx->setMaximumWeight(getMaximumWeight());
//   copymx->setHardWeight(getHardWeight());

//   return copymx;
// }

// Adds a new hard clause to the hard clause database.
void MaxSATFormula::addHardClause(Constraint *ctr, vec<Lit> &lits) {
  ctr->clause_ids.push(n_hard);
  hard_clauses.push();
  vec<Lit> copy_lits;
  lits.copyTo(copy_lits);
  new (&hard_clauses[hard_clauses.size() - 1]) Hard(copy_lits, 0);
  n_hard++;
}

// Adds a new soft clause to the hard clause database.
void MaxSATFormula::addSoftClause(uint64_t weight, vec<Lit> &lits) {
  soft_clauses.push();
  vec<Lit> vars;
  Lit assump = lit_Undef;
  vec<Lit> copy_lits;
  lits.copyTo(copy_lits);

  new (&soft_clauses[soft_clauses.size() - 1])
      Soft(copy_lits, weight, assump, vars);
  n_soft++;
}

// Adds a new soft clause to the hard clause database with predefined relaxation
// variables.
void MaxSATFormula::addSoftClause(uint64_t weight, vec<Lit> &lits,
                                  vec<Lit> &vars) {
  soft_clauses.push();
  Lit assump = lit_Undef;
  vec<Lit> copy_lits;
  lits.copyTo(copy_lits);

  new (&soft_clauses[soft_clauses.size() - 1])
      Soft(copy_lits, weight, assump, vars);
  n_soft++;
}

int MaxSATFormula::nInitialVars() {
  return n_initial_vars;
} // Returns the number of variables in the working MaxSAT formula.

void MaxSATFormula::setInitialVars(int vars) { n_initial_vars = vars; }

int MaxSATFormula::nVars() {
  return n_vars;
} // Returns the number of variables in the working MaxSAT formula.

int MaxSATFormula::nSoft() {
  return n_soft;
} // Returns the number of soft clauses in the working MaxSAT formula.

int MaxSATFormula::nHard() {
  return n_hard;
} // Returns the number of hard clauses in the working MaxSAT formula.

void MaxSATFormula::newVar(int v) {
  if (v == -1)
    n_vars++;
  else if (v > n_vars)
    n_vars = v;
} // Increases the number of variables in the working MaxSAT formula.

// Makes a new literal to be used in the working MaxSAT formula.
Lit MaxSATFormula::newLiteral(bool sign) {
  Lit p = mkLit(nVars(), sign);
  newVar();
  return p;
}

void MaxSATFormula::setProblemType(int type) {
  problem_type = type;
} // Sets the problem type.

int MaxSATFormula::getProblemType() {
  return problem_type; // Return the problem type.
}

// 'ubCost' is initialized to the sum of weights of the soft clauses.
void MaxSATFormula::updateSumWeights(uint64_t weight) {
  if (weight != hard_weight)
    sum_soft_weight += weight;
}

// The initial 'currentWeight' corresponds to the maximum weight of the soft
// clauses.
void MaxSATFormula::setMaximumWeight(uint64_t weight) {
  if (weight > max_soft_weight && weight != hard_weight)
    max_soft_weight = weight;
}

uint64_t MaxSATFormula::getMaximumWeight() { return max_soft_weight; }

void MaxSATFormula::setHardWeight(uint64_t weight) {
  hard_weight = weight;
} // Sets the weight of hard clauses.

Soft &MaxSATFormula::getSoftClause(int pos) {
  assert(pos < nSoft());
  return soft_clauses[pos];
}

Hard &MaxSATFormula::getHardClause(int pos) {
  assert(pos < nHard());
  return hard_clauses[pos];
}

void MaxSATFormula::addPBConstraint(PB *p) {

  // Add constraint to formula data structure.
  proof_log_id++;
  if (p->isEmpty()) {
    vec<Lit> empty;
    clause_ids.push(n_hard);
    addHardClause(p, empty);
  } else {

    if (p->isClause()) {
      if (p->_sign == _PB_EQUAL_) {
        assert(p->_lits.size() == 1);
        vec<Lit> unit;
        if (p->_rhs == 0)
          unit.push(~p->_lits[0]);
        else if (p->_rhs == 1)
          unit.push(p->_lits[0]);
        else
          assert(false);
        clause_ids.push(n_hard);
        addHardClause(p, unit);
      } else if (p->_sign == _PB_GREATER_OR_EQUAL_) {
        clause_ids.push(n_hard);
        addHardClause(p, p->_lits);
      } else {
        vec<Lit> neg_lits;
        for (int i = 0; i < p->_lits.size(); i++) {
          neg_lits.push(~p->_lits[i]);
        }
        clause_ids.push(n_hard);
        addHardClause(p, neg_lits);
      }
    } else if (p->isCardinality()) {
      cardinality_constraints.push(
          new Card(p->_lits, p->_rhs, p->_sign, proof_log_id));
    } else {
      // if (!p->_sign) {
      //   p->changeSign();
      // }

      // TODO: test PB constraints
      pb_constraints.push(
          new PB(p->_lits, p->_coeffs, p->_rhs, p->_sign, proof_log_id));
    }
    if (p->_sign == _PB_EQUAL_) {
      proof_log_id++;
    }
  }
}

int MaxSATFormula::newVarName(char *varName) {
  int id = varID(varName);
  if (id == var_Undef) {
    id = nVars();
    newVar();
    std::string s(varName);
    std::pair<std::string, int> nv(s, id);
    std::pair<int, std::string> ni(id, s);
    _nameToIndex.insert(nv);
    _indexToName.insert(ni);
    // parse xi variable from PB files
    // only works if the variables are of that kind
    assert(s[0] == 'x');
    std::string varId = s.substr(1, s.size());
    std::pair<int, int> vi(id, atoi(varId.c_str()));
    _varMap.insert(vi);
  }
  return id;
}

int MaxSATFormula::varID(char *varName) {
  std::string s(varName);

  nameMap::const_iterator iter = _nameToIndex.find(s);
  if (iter != _nameToIndex.end()) {
    return iter->second;
  }
  return var_Undef;
}

void MaxSATFormula::convertPBtoMaxSAT() {
  assert(objective_function != NULL);
  vec<Lit> unit_soft(1);

  // Convert objective function to soft clauses
  for (int i = 0; i < objective_function->_lits.size(); i++) {
    assert(objective_function->_coeffs[i] > 0);
    unit_soft[0] = ~objective_function->_lits[i];
    addSoftClause(objective_function->_coeffs[i], unit_soft);

    // Updates the maximum weight of soft clauses.
    setMaximumWeight(objective_function->_coeffs[i]);
    // Updates the sum of the weights of soft clauses.
    updateSumWeights(objective_function->_coeffs[i]);
  }

  if (getMaximumWeight() == 1)
    setProblemType(_UNWEIGHTED_);
  else
    setProblemType(_WEIGHTED_);
}

void MaxSATFormula::printCNFtoFile(std::string filename) {

  std::ofstream file;
  std::stringstream ss;
  file.open(filename + ".cnf");
  ss << "p cnf " << nVars() << " " << nHard() << "\n";

  for (int i = 0; i < nHard(); i++) {
    Hard &hard = getHardClause(i);
    hard.print(ss, getVarMap());
  }
  file << ss.rdbuf();
  file.close();
}

void MaxSATFormula::printPBPtoFile(std::string filename) {
  std::ofstream file;
  std::stringstream ss;
  file.open(filename + ".pbp");
  ss << "pseudo-Boolean proof version 1.2\nf\n";

  for (int i = 0; i < nCardinalityConstraint(); i++) {
    ss << "# 1\n";
    Card *card = getCardinalityConstraint(i);
    for (int j = 0; j < card->proof_expr_id.size(); j++) {
      PBP *pbp = getProofExpr(card->proof_expr_id[j]);
      pbp->print(ss, getVarMap());
    }
    ss << "# 0\n";
    for (int j = 0; j < card->clause_ids.size(); j++) {
      Hard &hard = getHardClause(card->clause_ids[j]);
      hard.printPBPu(ss, getVarMap());
    }
    ss << "w 1\n";
  }
  for (int i = 0; i < nPBConstraint(); i++) {
    ss << "# 1\n";
    PB *pb = getPBConstraint(i);
    for (int j = 0; j < pb->proof_expr_id.size(); j++) {
      PBP *pbp = getProofExpr(pb->proof_expr_id[j]);
      pbp->print(ss, getVarMap());
    }
    ss << "# 0\n";
    for (int j = 0; j < pb->clause_ids.size(); j++) {
      Hard &hard = getHardClause(pb->clause_ids[j]);
      hard.printPBPu(ss, getVarMap());
    }
    ss << "w 1\n";
  }
  for (int i = 0; i < clause_ids.size(); i++) {
    Hard &hard = getHardClause(clause_ids[i]);
    hard.printPBPu(ss, getVarMap());
  }

  file << ss.rdbuf();
  file.close();
}

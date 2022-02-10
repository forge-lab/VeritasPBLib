/*!
 * \author Ruben Martins - rubenm@andrew.cmu.edu
 *
 * @section LICENSE
 *
 * MiniSat,   Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
 *            Copyright (c) 2007-2010, Niklas Sorensson
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

#include "utils/Options.h"
#include "utils/ParseUtils.h"
#include "utils/System.h"
#include <errno.h>
#include <signal.h>
#include <zlib.h>

#include <fstream>
#include <iostream>
#include <map>
#include <stdlib.h>
#include <string>
#include <vector>

#include "core/Solver.h"

#include "MaxSAT.h"
#include "MaxTypes.h"
#include "ParserMaxSAT.h"
#include "ParserPB.h"
#include "encodings/Encodings.h"

using NSPACE::BoolOption;
using NSPACE::cpuTime;
using NSPACE::IntOption;
using NSPACE::IntRange;
using NSPACE::OutOfMemoryException;
using NSPACE::parseOptions;
using NSPACE::StringOption;
using namespace openwbo;

//=================================================================================================

static MaxSAT *mxsolver;

static void SIGINT_exit(int signum) {
  mxsolver->printAnswer(_UNKNOWN_);
  exit(_UNKNOWN_);
}

//=================================================================================================
// Main:

int main(int argc, char **argv) {
  printf("c\nc VeritasPBLib:\t Verified PB encodings\n");
  printf("c Version:\t February 2022\n");
  printf("c Authors:\t Stephan Gocht, Andy Oertel, Ruben Martins, Jakob "
         "Nordstrom\n");
  printf("c Contact:\t rubenm@andrew.cmu.edu\nc\n");
  NSPACE::setUsageHelp("c USAGE: %s [options] <input-file>\n\n");

  IntOption cardinality("VeritasPBLib", "card",
                        "Cardinality encoding (0=sequential, "
                        "1=totalizer).\n",
                        0, IntRange(0, 1));

  IntOption pseudoboolean("VeritasPBLib", "pb",
                          "PB encoding (0=GTE, 1=adder).\n", 0, IntRange(0, 1));

  BoolOption stats("VeritasPBLib", "stats",
                   "Statistics for cardinality constraints", 0);

  BoolOption verified("VeritasPBLib", "verified",
                      "Uses the verified version of the encoding", 1);


  BoolOption proof("VeritasPBLib", "proof",
                   "Stores information and writes the proof to file", 1);

  parseOptions(argc, argv, true);

  double initial_time = cpuTime();

  signal(SIGXCPU, SIGINT_exit);
  signal(SIGTERM, SIGINT_exit);

  if (argc == 1) {
    printf("c Warning: no filename.\n");
  }

  gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
  if (in == NULL)
    printf("c ERROR! Could not open file: %s\n",
           argc == 1 ? "<stdin>" : argv[1]),
        printf("s UNKNOWN\n"), exit(_ERROR_);

  MaxSATFormula *maxsat_formula = new MaxSATFormula();
  ParserPB *parser_pb = new ParserPB();
  parser_pb->parsePBFormula(argv[1], maxsat_formula);
  maxsat_formula->setFormat(_FORMAT_PB_);
  gzclose(in);

  printf("c |                                                                "
         "                                       |\n");
  printf("c ========================================[ Problem Statistics "
         "]===========================================\n");
  printf("c |                                                                "
         "                                       |\n");

  printf("c |  Problem Format:  %17s                                         "
         "                          |\n",
         "PB");

  printf("c |  Number of variables:  %12d                                    "
         "                               |\n",
         maxsat_formula->nVars());
  printf("c |  Number of hard clauses:    %7d                                "
         "                                   |\n",
         maxsat_formula->nHard());
  printf("c |  Number of cardinality:     %7d                                "
         "                                   |\n",
         maxsat_formula->nCard());
  printf("c |  Number of PB :             %7d                                "
         "                                   |\n",
         maxsat_formula->nPB());
  double parsed_time = cpuTime();

  printf("c |  Parse time:           %12.2f s                                "
         "                                 |\n",
         parsed_time - initial_time);
  printf("c |                                                                "
         "                                       |\n");

  pb_Cardinality card;
  pb_PB pb;

  switch ((int)cardinality) {
  case 0:
    if (verified) {
      card = _CARD_VSEQUENTIAL_;
      printf("c Cardinality encoding: verified sequential\n");
    } else {
      card = _CARD_SEQUENTIAL_;
      printf("c Cardinality encoding: sequential\n");
    }
    break;
  case 1:
    if (verified) {
      card = _CARD_VTOTALIZER_;
      printf("c Cardinality encoding: verified totalizer\n");
    } else {
      card = _CARD_TOTALIZER_;
      printf("c Cardinality encoding: totalizer\n");
    }
    break;
  default:
    assert(false);
  }

  switch ((int)pseudoboolean) {
  case 0:
    if (verified) {
      pb = _PB_VGTE_;
      printf("c PB encoding: verified GTE\n");
    } else {
      pb = _PB_GTE_;
      printf("c PB encoding: GTE\n");
    }
    break;
  case 1:
    if (verified) {
      pb = _PB_VADDER_;
      printf("c PB encoding: verified adder\n");
    } else {
      pb = _PB_ADDER_;
      printf("c PB encoding: adder\n");
    }
    break;
  default:
    assert(false);
  }

  if (!stats) {

    Encodings *encoder = new Encodings(card, pb);

    for (int i = 0; i < maxsat_formula->nCard(); i++) {
      Card *c = maxsat_formula->getCardinalityConstraint(i);
      encoder->encode(c, maxsat_formula, (int)proof==1);
      maxsat_formula->bumpProofLogId(c->clause_ids.size());
    }

    for (int i = 0; i < maxsat_formula->nPB(); i++) {
      PB *p = maxsat_formula->getPBConstraint(i);
      encoder->encode(p, maxsat_formula, (int)proof==1);
      maxsat_formula->bumpProofLogId(p->clause_ids.size());
    }

    std::string filename(argv[1]);
    filename = filename.substr(0, filename.find_last_of("."));

    maxsat_formula->printCNFtoFile(filename);
    if (proof) {
      maxsat_formula->printPBPtoFile(filename);
    }

    std::cout << "c CNF file " << filename << ".cnf" << std::endl;
    if (proof) {
      std::cout << "c PBP file " << filename << ".pbp" << std::endl;
    }

  } else {

    if (maxsat_formula->nCard() > 0) {

      int min = -1;
      int max = -1;
      int avg = 0;
      float ratio = 0.0;

      for (int i = 0; i < maxsat_formula->nCard(); i++) {
        Card *c = maxsat_formula->getCardinalityConstraint(i);
        if (c->_lits.size() < min || min == -1)
          min = c->_lits.size();
        if (c->_lits.size() > max)
          max = c->_lits.size();
        avg += c->_lits.size();
        // assumes that we can always convert <= to >= to have a smaller
        // encoding
        float r = (float)c->_rhs / c->_lits.size();
        if (r > 0.5)
          ratio += 1 - r;
        else
          ratio += r;
      }

      std::cout << "c === Cardinality stats ===" << std::endl;
      std::cout << "c | Card - min size: " << min << std::endl;
      std::cout << "c | Card - max size: " << max << std::endl;
      std::cout << "c | Card - avg size: " << (avg / maxsat_formula->nCard())
                << std::endl;
      std::cout << "c | Card - ratio: "
                << (float)ratio / maxsat_formula->nCard() << std::endl;
    }

    if (maxsat_formula->nPB() > 0) {

      int min = -1;
      int max = -1;
      int avg = 0;
      int64_t max_coeff = -1;
      int64_t min_coeff = -1;
      float avg_coeff = 0;

      for (int i = 0; i < maxsat_formula->nPB(); i++) {
        PB *c = maxsat_formula->getPBConstraint(i);
        if (c->_lits.size() < min || min == -1)
          min = c->_lits.size();
        if (c->_lits.size() > max)
          max = c->_lits.size();
        avg += c->_lits.size();
        int64_t c_avg_coeff = 0;
        for (int j = 0; j < c->_coeffs.size(); j++) {
          if (c->_coeffs[j] < min_coeff || min_coeff == -1)
            min_coeff = c->_coeffs[j];
          if (c->_coeffs[j] > max_coeff)
            max_coeff = c->_coeffs[j];
          c_avg_coeff += c->_coeffs[j];
        }
        avg_coeff += ((float)c_avg_coeff / c->_lits.size());
      }

      std::cout << "c === PB stats ===" << std::endl;
      std::cout << "c | PB - min size: " << min << std::endl;
      std::cout << "c | PB - max size: " << max << std::endl;
      std::cout << "c | PB - avg size: " << (avg / maxsat_formula->nPB())
                << std::endl;
      std::cout << "c | PB - min coeff size: " << min_coeff << std::endl;
      std::cout << "c | PB - max coeff size: " << max_coeff << std::endl;
      std::cout << "c | PB - avg coeff size: "
                << (avg_coeff / maxsat_formula->nPB()) << std::endl;
    }
  }

  return 0;
}

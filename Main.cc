/*!
 * \author Ruben Martins - rubenm@andrew.cmu.edu
 *
 * @section LICENSE
 *
 * MiniSat,   Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
 *            Copyright (c) 2007-2010, Niklas Sorensson
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

using NSPACE::cpuTime;
using NSPACE::OutOfMemoryException;
using NSPACE::IntOption;
using NSPACE::BoolOption;
using NSPACE::StringOption;
using NSPACE::IntRange;
using NSPACE::parseOptions;
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
  printf("c Version:\t 2021\n");
  printf("c Authors:\t Ruben Martins, Stephan Gocht, Jakob Nordstrom\n");
  printf("c Contact:\t rubenm@andrew.cmu.edu\nc\n");
  NSPACE::setUsageHelp("c USAGE: %s [options] <input-file>\n\n");

    IntOption cardinality("VeritasPBLib", "card",
                          "Cardinality encoding (0=sequential, "
                          "1=totalizer, 2=adder).\n", 0, IntRange(0, 2));

    IntOption pseudoboolean("VeritasPBLib", "pb", "PB encoding (0=sequential,1=totalizer, 2=adder).\n", 
                  2,IntRange(0, 2));

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

    printf(
          "c |  Problem Format:  %17s                                         "
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

    switch(cardinality){
       case 0: 
         card = _CARD_SEQUENTIAL_;
         printf("c Cardinality encoding: sequential\n");
         break;
       case 1:
         card = _CARD_TOTALIZER_;
         printf("c Cardinality encoding: totalizer\n");
         break;
       case 2:
         card = _CARD_ADDER_;
         printf("c Cardinality encoding: adder\n");
         break;
       default:
         assert(false);
    }

    switch(pseudoboolean){
       case 0: 
         pb = _PB_SWC_;
         printf("c PB encoding: SWC\n");
         break;
       case 1:
         pb = _PB_GTE_;
         printf("c PB encoding: GTE\n");
         break;
       case 2:
         pb = _PB_ADDER_;
         printf("c PB encoding: adder\n");
         break;
       default:
         assert(false);
    }

   
   Encodings * encoder = new Encodings(card, pb);


   for(int i = 0; i < maxsat_formula->nCard(); i++){
        Card * c = maxsat_formula->getCardinalityConstraint(i);
        encoder->encode(c, maxsat_formula);
   }

   for (int i = 0; i < maxsat_formula->nPB(); i++){
        PB * p = maxsat_formula->getPBConstraint(i);
        encoder->encode(p, maxsat_formula);
   }

   std::string filename(argv[1]);
   filename = filename.substr(0, filename.find_last_of("."));

   maxsat_formula->printCNFtoFile(filename);
   maxsat_formula->printPBPtoFile(filename);
   
   std::cout << "c CNF file " << filename << ".cnf" << std::endl;
   std::cout << "c PBP file " << filename << ".pbp" << std::endl;


   return 0;
}

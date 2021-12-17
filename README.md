# VeritasPBLib

## Usage

```./VeritasPBLib filename.opb```

Expected to write two files `filename.cnf` and `filename.pbp`. The first file contains the CNF encoding of the OPB file. The second file contains the proof logging information that can be checked with `VeriPB`.

### Options
-card=<int>
	0=sequential
	1=totalizer

* Selects which cardinality encoding to use	

-pb=<int>
	0=GTE
	1=adder

* Selects which pseudo-Boolean encoding to use

-no-verified

* Selects if it uses the verified or unverified version of the encoding; The default is the verified version where a .pbp file is created with the proof log.

-stats

* Prints some statistics of the cardinality constraints in the OPB formula.

## CNF encodings
Useful functions and classes:
* `Encodings.cc`: contains functions to add unit, binary, ternary, quaternary, and other size of clauses. It will automatically increase the ID of the constraint that was created.

* `maxsat_formula->newVar()`: creates a new variable in the CNF

* `mkLit(id, true/fase)`: uses the minisat structure of literals to create new literals (useful when creating auxiliary variables)

* `FormulaPB.h`: contains the functions and classes for cardinality and pseudo-Boolean

## Verified encodings

* `FormulaVeriPB.h`: contains the functions for the verified logging. `PBPred` and `PBPp` are the more useful classes that will be used in the proof log.


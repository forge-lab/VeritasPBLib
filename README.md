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

* Example of using `PBPred` to store a proof rule:
	+ Construct a PB constraint. For instance, suppose you want a constraint `1 x1 1 x4 >= 1;`  This can be done by building a vector of literals (vec<Lit> lits) and a vector of coefficients (vec<int64_t> coeffs) and then calling the PB constructor (e.g., `PB * pb = new PB(lits,  coeffs, rhs, _PB_GREATER_OR_EQUAL_`, where rhs=1 for this constraint). 
	+ Construct a PBPred constraint. Example: `PBPred * pbp = new PBPred(id, pb, v, value`, where id corresponds to a fresh id (you get can a new one with maxsat_formula->getIncId()), pb is the pseudo-Boolean constraint, v is the witness variable and value is 0 or 1.
	+ Add this proof constraint to the database of proof constraints. You can do this by using `maxsat_formula->addProofExpr(pbp)`.

* Example of using `PBPp` to store a proof rule:
	+ Construct a PBPp constraint with the PBPp constructor (e.g., `PBPp * pbp = new PBPp(id)`), where id correspond to a fresh id (recall that you can get a fresh id with the method maxsat_formula->getIncId()).
	+ Use the addition, multiplication and division methods from the PBPp to construct the constraint using the polish notation. 
	+ Add this proof constraint to the database of proof constraints. You can do this by using `maxsat_formula->addProofExpr(pbp)`.

* Note that the RUP constraints will be automatically added using the CNF encoding that you generate and you do not need to manually add them to the proof constraint database. 



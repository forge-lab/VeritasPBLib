SOLVER     ?= minisat2.2
#
include $(PWD)/solvers/$(SOLVER).mk

EXEC       = VeritasPBLib
DEPDIR     += mtl utils core
DEPDIR     +=  ../../encodings ../../algorithms ../../graph ../../classifier
MROOT      ?= $(PWD)/solvers/$(SOLVERDIR)
LFLAGS     += -lgmpxx -lgmp --sanitize=address
CFLAGS     += -Wall -Wno-parentheses -std=c++11 -DNSPACE=$(NSPACE) -DSOLVERNAME=$(SOLVERNAME) -DVERSION=$(VERSION) --sanitize=address

include $(MROOT)/mtl/template.mk

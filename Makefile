MODULES := CoqEqDec Coqlib Util VectorClocks block_model conc_model Lang HBRaceDetector HBSim SCFacts ExecFacts HBReorder
VS := $(MODULES:%=%.v)

#COQFLAGS := -R /cygdrive/c/Users/William/Documents/GitHub/compcomp compcert

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile $(COQFLAGS) $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

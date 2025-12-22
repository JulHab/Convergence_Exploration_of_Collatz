COQC=coqc
COQFLAGS=-Q src Collatz

all:
	$(COQC) $(COQFLAGS) src/LocalLemmas.v
	$(COQC) $(COQFLAGS) src/CollatzCore.v
	$(COQC) $(COQFLAGS) src/CollatzBase.v
	$(COQC) $(COQFLAGS) src/CollatzIter.v
	$(COQC) $(COQFLAGS) src/BridgeGlobal.v
	$(COQC) $(COQFLAGS) src/CheckerSpec.v
	$(COQC) $(COQFLAGS) src/MainTheorem.v
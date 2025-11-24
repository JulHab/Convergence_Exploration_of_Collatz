COQC=coqc
COQFLAGS=-Q src Collatz

all:
	$(COQC) $(COQFLAGS) src/CollatzBase.v
	$(COQC) $(COQFLAGS) src/CollatzState.v
	$(COQC) $(COQFLAGS) src/CollatzCertificate.v
	$(COQC) $(COQFLAGS) src/CertificateChecker.v
	$(COQC) $(COQFLAGS) src/CertificateData.v
	$(COQC) $(COQFLAGS) src/MainTheorem.v
	$(COQC) $(COQFLAGS) src/BoundedDescentSound.v
	$(COQC) $(COQFLAGS) src/LocalLemmas.v
	$(COQC) $(COQFLAGS) src/CollatzGlobal.v
	

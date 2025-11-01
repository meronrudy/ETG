COQMAKEFILE := Makefile.coq
VFILES := Base.v Metric.v DETG.v Frames.v Invariance.v PETG.v GETG.v Examples.v

all: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) all

$(COQMAKEFILE): $(VFILES)
	coq_makefile -o $(COQMAKEFILE) $(VFILES)

clean:
	@if [ -f $(COQMAKEFILE) ]; then $(MAKE) -f $(COQMAKEFILE) clean; fi
	@rm -f $(COQMAKEFILE)

.PHONY: all clean

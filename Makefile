VFILES := $(shell find . -name "*.v" -type f -not -path "./reference/*")

default: coq

CoqMakefile:
	coq_makefile -f _CoqProject -o CoqMakefile $(VFILES)

coq: CoqMakefile
	$(MAKE) -f CoqMakefile all

clean:
	find . -name "*.vo"    -type f -delete
	find . -name "*.aux"   -type f -delete
	find . -name "*.vos"   -type f -delete
	find . -name "*.vok"   -type f -delete
	find . -name "*.glob"  -type f -delete
	find . -name "*.cache" -type f -delete

distclean: clean
	rm -f CoqMakefile CoqMakefile.conf .CoqMakefile.d .coqdeps.d

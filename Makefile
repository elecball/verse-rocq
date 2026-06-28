.PHONY: all clean

all: CoqMakefile
	$(MAKE) -f CoqMakefile

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

clean:
	$(MAKE) -f CoqMakefile clean
	rm -f CoqMakefile CoqMakefile.conf

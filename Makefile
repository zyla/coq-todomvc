all: coq
.PHONY: all clean

%: Makefile.coq
	+$(MAKE) -f Makefile.coq $@

coq: Makefile.coq
	+$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	+$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject -o Makefile.coq

# Avoid circular dependencies
_CoqProject: ;
Makefile: ;

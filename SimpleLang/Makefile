# Forward most targets to Coq makefile (with some trick to make this phony)
%: Makefile.coq phony
	+@make -f Makefile.coq $@

all: Makefile.coq
	+@make -f Makefile.coq all
.PHONY: all

clean: Makefile.coq
	+@make -f Makefile.coq clean
	rm -f Makefile.coq
.PHONY: clean

# Create Coq Makefile.
Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject -o Makefile.coq

# Some files that do *not* need to be forwarded to Makefile.coq
Makefile: ;
_CoqProject: ;

# Phony wildcard targets
phony: ;
.PHONY: phony

.PHONY: clean all jscoq32 jscoq64

COQDIR=~/external/coq-git/

all:

# Include coq files
INCLUDETOP=-I $(COQDIR)/library/ -I $(COQDIR)/stm/ -I $(COQDIR)/lib/ -I $(COQDIR)/parsing/ -I $(COQDIR)/printing/ -I $(COQDIR)/kernel/ -I $(COQDIR)/proofs/ -I $(COQDIR)/toplevel -I $(COQDIR)/config

# CAMLDEBUG=-g
CAMLDEBUG=
BYTEFLAGS=-rectypes -safe-string $(CAMLDEBUG)

JSOOFLAGS=-syntax camlp4o -package js_of_ocaml.syntax,js_of_ocaml.tyxml
JSOOFLAGS+=-package yojson,js_of_ocaml.compiler,js_of_ocaml.toplevel
# For when we remove dyncomp
# JSOOFLAGS+=-package yojson

# Our OCAML rules, we could refine the includes
%.cmi: %.mli
	ocamlfind ocamlc -c $(BYTEFLAGS) $(INCLUDETOP) $(JSOOFLAGS) $<

%.cmo: %.ml
	ocamlfind ocamlc -c $(BYTEFLAGS) $(INCLUDETOP) $(JSOOFLAGS) $<

########################################################################
# Main jscoq files
icoq.cmo: icoq.cmi

# No mli file
# jslib.cmo: jslib.cmi

jslog.cmo: jslog.cmi

jslibmng.cmo: icoq.cmo jslib.cmo jslog.cmo jslibmng.cmi

# Main file
jscoq.cmi: jscoq.mli
jscoq.cmo: icoq.cmo jslibmng.cmo jslog.cmo jscoq.cmi

COQDEPS=$(COQDIR)/lib/clib.cma			\
	$(COQDIR)/lib/lib.cma			\
	$(COQDIR)/kernel/byterun/dllcoqrun.so	\
	$(COQDIR)/kernel/kernel.cma		\
	$(COQDIR)/library/library.cma		\
	$(COQDIR)/engine/engine.cma		\
	$(COQDIR)/pretyping/pretyping.cma	\
	$(COQDIR)/interp/interp.cma		\
	$(COQDIR)/proofs/proofs.cma		\
	$(COQDIR)/parsing/parsing.cma		\
	$(COQDIR)/printing/printing.cma		\
	$(COQDIR)/tactics/tactics.cma		\
	$(COQDIR)/stm/stm.cma			\
	$(COQDIR)/toplevel/toplevel.cma		\
	$(COQDIR)/parsing/highparsing.cma	\
	$(COQDIR)/tactics/hightactics.cma

# -linkall is delicate here due the way js_of_ocaml works.
# jscoq.byte: $(COQDEPS) jscoq.cmo
# 	ocamlfind ocamlc $(BYTEFLAGS) -linkall -linkpkg -thread -verbose \
# 	   $(JSOOFLAGS) -package camlp5                                  \
# 	   dynlink.cma str.cma gramlib.cma $(COQDEPS) jslib.cmo icoq.cmo jslog.cmo jslibmng.cmo jscoq.cmo -o jscoq.byte

jscoq.byte: $(COQDEPS) jscoq.cmo jsoo_dl.cmo
	ocamlfind ocamlc $(BYTEFLAGS) -linkall -linkpkg -thread -verbose \
	   $(JSOOFLAGS) -package camlp5                                  \
	   dynlink.cma str.cma gramlib.cma $(COQDEPS) jslib.cmo icoq.cmo jslog.cmo jslibmng.cmo jsoo_dl.cmo jscoq.cmo -o jscoq.byte

jscoq32: jscoq.byte

########################################################################
# Compilation to JS

# JSFILES=mutex.js unix.js coq_vm.js aux.js
JSDIR=../lib-js
JSFILES=$(JSDIR)/mutex.js $(JSDIR)/unix.js $(JSDIR)/coq_vm.js $(JSDIR)/byte_cache.js

# JSLIBFILES=nsp.js
# jscoq.js: jscoq.byte $(JSFILES) $(JSLIBFILES)

# JSOO_OPTS=--pretty --noinline --disable shortvar --debug-info
# JSOO_OPTS=-opt 3
JSOO_OPTS=

# --toplevel includes the linking information.
jscoq.js: jscoq.byte $(JSFILES)
	js_of_ocaml $(JSOO_OPTS) --toplevel --nocmis +nat.js +weak.js +dynlink.js +toplevel.js $(JSFILES) jscoq.byte

# For when we remove dyncomp
# js_of_ocaml $(JSOO_OPTS) +nat.js +weak.js +dynlink.js +toplevel.js $(JSFILES) jscoq.byte
# js_of_ocaml $(JSOO_OPTS) --toplevel --nocmis +nat.js +weak.js +dynlink.js +toplevel.js $(JSFILES) jscoq.byte

jscoq64: jscoq.js

clean:
	rm -f *.cmi *.cmo *.ml.d *.mli.d jscoq.byte jscoq.js

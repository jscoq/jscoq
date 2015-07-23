.PHONY: clean upload libs all

COQDIR=~/external/coq-git/

all: jscoqtop.js

# Include coq files
INCLUDETOP=-I $(COQDIR)/library/ -I $(COQDIR)/stm/ -I $(COQDIR)/lib/ -I $(COQDIR)/parsing/ -I $(COQDIR)/printing/ -I $(COQDIR)/kernel/ -I $(COQDIR)/proofs/ -I $(COQDIR)/toplevel

# CAMLDEBUG=-g
CAMLDEBUG=
BYTEFLAGS=-rectypes -safe-string $(CAMLDEBUG)

JSOOFLAGS=-syntax camlp4o -package js_of_ocaml.syntax,js_of_ocaml.tyxml
JSOOFLAGS+=-package js_of_ocaml.compiler,js_of_ocaml.toplevel

# Our OCAML rules, we could refine the includes
%.cmi: %.mli
	ocamlfind ocamlc -c $(BYTEFLAGS) $(INCLUDETOP) $(JSOOFLAGS) $<

%.cmo: %.ml
	ocamlfind ocamlc -c $(BYTEFLAGS) $(INCLUDETOP) $(JSOOFLAGS) $<

jscoq.cmi: jslib.cmo
jscoq.cmo: jscoq.cmi

# Binary for lib geneation
coqjslib.cmo: jslib.cmo

coqjslib: jslib.cmo coqjslib.cmo
	ocamlfind ocamlc $(BYTEFLAGS) jslib.cmo coqjslib.cmo -o coqjslib

jslog.cmo: jslog.cmi

jslibmng.cmo: jslibmng.cmi jslog.cmo

# Main file
jscoqtop.cmo: jscoq.cmo jslibmng.cmo jslog.cmo

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
jscoqtop.byte: $(COQDEPS) jscoqtop.cmo
	ocamlfind ocamlc $(BYTEFLAGS) -linkall -linkpkg -thread -verbose \
	   $(JSOOFLAGS) -package camlp5                                  \
	   dynlink.cma str.cma gramlib.cma $(COQDEPS) jslib.cmo jscoq.cmo jslog.cmo jslibmng.cmo jscoqtop.cmo -o jscoqtop.byte

# jscoqtop.byte: $(COQDEPS) jscoq.cmo jscoqtop.cmo
# 	ocamlfind ocamlc $(BYTEFLAGS) -linkall -linkpkg -thread -verbose -I +camlp5			\
# 	  -package unix -package compiler-libs.bytecomp -package compiler-libs.toplevel			\
# 	  -package js_of_ocaml.compiler -package camlp5 -package base64 -package js_of_ocaml.tyxml	\
# 	   dynlink.cma str.cma gramlib.cma $(COQDEPS) jslib.cmo jscoq.cmo jslibmng.cmo jscoqtop.cmo -o jscoqtop.byte

jscoq32: jscoqtop.byte

# JSFILES=mutex.js unix.js coq_vm.js aux.js
JSDIR=js
# JSFILES=$(JSDIR)/mutex.js $(JSDIR)/unix.js $(JSDIR)/coq_vm.js $(JSDIR)/ml_aux.js
JSFILES=$(JSDIR)/mutex.js $(JSDIR)/unix.js $(JSDIR)/coq_vm.js $(JSDIR)/byte_cache.js

# JSLIBFILES=nsp.js
# jscoqtop.js: jscoqtop.byte $(JSFILES) $(JSLIBFILES)

# JSOO_OPTS=--pretty --noinline --disable shortvar --debug-info
# JSOO_OPTS=-opt 3
JSOO_OPTS=

# --toplevel includes the linking information.
jscoqtop.js: jscoqtop.byte $(JSFILES)
	js_of_ocaml $(JSOO_OPTS) --toplevel --nocmis +nat.js +weak.js +dynlink.js +toplevel.js $(JSFILES) jscoqtop.byte

jscoq64: jscoqtop.js

########################################################################
# Plugin building + base64 encoding

filesys:
	mkdir -p filesys

Makefile.libs: coqjslib
	./coqjslib > Makefile.libs

libs: Makefile.libs
	COQDIR=$(COQDIR) make -f Makefile.libs libs-auto

# ssreflect not built by default for now
SSRDIR=~/external/coq/ssr-git/
SSR_PLUG=$(SSRDIR)/src/ssreflect.cma
SSR=$(SSRDIR)/theories/*.vo
SSR_DEST=filesys/ssr

filesys/ssr:
	mkdir -p filesys/ssr

ssr: filesys/ssr $(SSR_PLUG) $(SSR)
	$(shell cat $(SSR_PLUG) > filesys/ssreflect.cma)
	$(shell for i in $(SSR); do cat $$i > $(SSR_DEST)/`basename $$i`; done)

clean:
	rm -f *.cmi *.cmo *.ml.d *.mli.d jscoqtop.byte jscoqtop.js coqtop.byte coqtop.js Makefile.libs coqjslib
	rm -rf filesys

########################################################################
# Local stuff
upload: all
	rsync --delete -avzp index.html jscoqtop.js filesys css ejs ~/x80/rhino-coq/
# $(shell ./x80-sync.sh)

pau:
	rsync -avpz ~/research/jscoq pau:~/
	rsync -avpz pau:~/jscoq/ ~/research/pau-jscoq/

########################################################################
# Obsolete coptop stuff

COQTOP=$(COQDIR)/bin/coqtop.byte
NODEFILES=$(JSDIR)/fsInput.js

coqtop.byte: $(COQTOP)
	cp $(COQTOP) ./

coqtop.js: coqtop.byte jscoqtop.js $(JSFILES) $(NODEFILES)
	js_of_ocaml $(JSOO_OPTS) +nat.js +weak.js +dynlink.js +toplevel.js $(JSFILES) $(NODEFILES) coqtop.byte

# print_cmo: print_cmo.ml
# 	ocamlc.opt -I /home/egallego/external/js_of_ocaml/compiler print_cmo.ml -o print_cmo

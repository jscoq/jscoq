.PHONY: clean upload

# COQDIR=../coq-git/
COQDIR=~/external/coq-git/

all: jscoqtop.js

# Include coq files
INCLUDETOP=-I $(COQDIR)/library/ -I $(COQDIR)/stm/ -I $(COQDIR)/lib/ -I $(COQDIR)/parsing/ -I $(COQDIR)/printing/ -I $(COQDIR)/kernel/ -I $(COQDIR)/proofs/

CAMLDEBUG=-g
BYTEFLAGS=-rectypes $(CAMLDEBUG)

jscoq.cmi: jscoq.mli
	ocamlc -c $(BYTEFLAGS) $(INCLUDETOP) jscoq.mli

jscoq.cmo: jscoq.cmi jscoq.ml
	ocamlc -c $(BYTEFLAGS) $(INCLUDETOP) jscoq.ml

jscoqtop.cmo: jscoq.cmi jscoqtop.ml
	ocamlfind ocamlc -c $(BYTEFLAGS) -syntax camlp4o -package bytes -package js_of_ocaml.syntax,lwt,js_of_ocaml.tyxml,js_of_ocaml.toplevel -package base64 -I camlp4 -package ocp-indent.lib -package higlo.ocaml jscoqtop.ml

COQDEPS=$(COQDIR)/lib/clib.cma $(COQDIR)/lib/lib.cma $(COQDIR)/kernel/byterun/dllcoqrun.so $(COQDIR)/kernel/kernel.cma $(COQDIR)/library/library.cma $(COQDIR)/engine/engine.cma $(COQDIR)/pretyping/pretyping.cma $(COQDIR)/interp/interp.cma $(COQDIR)/proofs/proofs.cma $(COQDIR)/parsing/parsing.cma $(COQDIR)/printing/printing.cma $(COQDIR)/tactics/tactics.cma $(COQDIR)/stm/stm.cma $(COQDIR)/toplevel/toplevel.cma $(COQDIR)/parsing/highparsing.cma $(COQDIR)/tactics/hightactics.cma

# -linkall is delicate here due the way js_of_ocaml works.
jscoqtop.byte: $(COQDEPS) jscoq.cmo jscoqtop.cmo
	ocamlfind ocamlc $(BYTEFLAGS) -linkall -linkpkg -thread -verbose -I +camlp5 \
	  -package unix -package compiler-libs.bytecomp -package compiler-libs.toplevel \
	  -package js_of_ocaml.compiler -package camlp5 -package base64 -package js_of_ocaml.tyxml \
	   dynlink.cma str.cma gramlib.cma $(COQDEPS) jscoq.cmo jscoqtop.cmo -o jscoqtop.byte

jscoq32: jscoqtop.byte

# JSFILES=mutex.js unix.js coq_vm.js aux.js
JSDIR=js
# JSFILES=$(JSDIR)/mutex.js $(JSDIR)/unix.js $(JSDIR)/coq_vm.js $(JSDIR)/ml_aux.js
JSFILES=$(JSDIR)/mutex.js $(JSDIR)/unix.js $(JSDIR)/coq_vm.js

# JSLIBFILES=nsp.js
# jscoqtop.js: jscoqtop.byte $(JSFILES) $(JSLIBFILES)

# JSOO_OPTS=--pretty --noinline --disable shortvar --debug-info
# JSOO_OPTS=-opt 3
JSOO_OPTS=

# --toplevel includes the linking information.
jscoqtop.js: jscoqtop.byte $(JSFILES)
	js_of_ocaml $(JSOO_OPTS) --toplevel --nocmis +nat.js +weak.js +dynlink.js +toplevel.js $(JSFILES) jscoqtop.byte

jscoq64: jscoqtop.js

COQTOP=$(COQDIR)/bin/coqtop.byte
NODEFILES=$(JSDIR)/fsInput.js

coqtop.byte: $(COQTOP)
	cp $(COQTOP) ./

coqtop.js: coqtop.byte jscoqtop.js $(JSFILES) $(NODEFILES)
	js_of_ocaml $(JSOO_OPTS) +nat.js +weak.js +dynlink.js +toplevel.js $(JSFILES) $(NODEFILES) coqtop.byte

# print_cmo: print_cmo.ml
# 	ocamlc.opt -I /home/egallego/external/js_of_ocaml/compiler print_cmo.ml -o print_cmo

########################################################################
# Plugin building + base64 encoding

filesys:
	mkdir -p filesys

filesys/coq_init:
	mkdir -p filesys/coq_init

filesys/coq_bool:
	mkdir -p filesys/coq_bool

filesys/ssr:
	mkdir -p filesys/ssr

lib-dirs: filesys filesys/coq_init filesys/coq_bool filesys/ssr

COQPDIR=$(COQDIR)/plugins
COQ_PLUGINS=$(COQPDIR)/syntax/nat_syntax_plugin.cma	\
	$(COQPDIR)/decl_mode/decl_mode_plugin.cma	\
	$(COQPDIR)/cc/cc_plugin.cma			\
	$(COQPDIR)/firstorder/ground_plugin.cma

# Disabled for performance reasons
# $(COQPDIR)/funind/recdef_plugin.cma		\
# $(COQPDIR)/extraction/extraction_plugin.cma

# Not enabled for now.
# micromega/micromega_plugin.cma
# rtauto/rtauto_plugin.cma
# setoid_ring/newring_plugin.cma
# syntax/string_syntax_plugin.cma
# syntax/r_syntax_plugin.cma
# syntax/z_syntax_plugin.cma
# syntax/ascii_syntax_plugin.cma
# quote/quote_plugin.cma
# omega/omega_plugin.cma
# btauto/btauto_plugin.cma
# fourier/fourier_plugin.cma
# nsatz/nsatz_plugin.cma
# derive/derive_plugin.cma
# romega/romega_plugin.cma

COQ_PLUGINS_DEST=filesys

plugins: $(COQ_PLUGINS)
	$(shell for i in $(COQ_PLUGINS); do base64 $$i > $(COQ_PLUGINS_DEST)/`basename $$i`; done)

# Note: this has to match the hiearchy we set in jscoq.ml
# We'll rewrite this part anyways.

COQTDIR=$(COQDIR)/theories

COQ_INIT=$(COQTDIR)/Init/Notations.vo		\
	 $(COQTDIR)/Init/Tactics.vo		\
	 $(COQTDIR)/Init/Logic.vo		\
	 $(COQTDIR)/Init/Logic_Type.vo		\
	 $(COQTDIR)/Init/Datatypes.vo		\
	 $(COQTDIR)/Init/Nat.vo  		\
	 $(COQTDIR)/Init/Peano.vo  		\
	 $(COQTDIR)/Init/Specif.vo  		\
	 $(COQTDIR)/Init/Wf.vo  		\
	 $(COQTDIR)/Init/Prelude.vo

COQ_INIT_DEST=filesys/coq_init

coq_init: $(COQ_INIT)
	$(shell for i in $(COQ_INIT); do base64 $$i > $(COQ_INIT_DEST)/`basename $$i`; done)

COQ_BOOL=$(COQTDIR)/Bool/Bool.vo

COQ_BOOL_DEST=filesys/coq_bool
coq_bool: $(COQ_BOOL)
	$(shell for i in $(COQ_BOOL); do base64 $$i > $(COQ_BOOL_DEST)/`basename $$i`; done)


libs: lib-dirs plugins coq_init coq_bool

# Not built by default for now: ssreflect
SSRDIR=~/external/coq/ssr-git/

SSR_PLUG=$(SSRDIR)/src/ssreflect.cma

SSR=$(SSRDIR)/theories/ssrmatching.vo	\
	$(SSRDIR)/theories/ssreflect.vo  \
	$(SSRDIR)/theories/ssrfun.vo     \
	$(SSRDIR)/theories/ssrbool.vo    \
	$(SSRDIR)/theories/eqtype.vo     \
	$(SSRDIR)/theories/ssrnat.vo

SSR_DEST=filesys/ssr

ssr: $(SSR_PLUG) $(SSR)
	$(shell base64 $(SSR_PLUG) > $(COQ_PLUGINS_DEST)/ssreflect.cma)
	$(shell for i in $(SSR); do base64 $$i > $(SSR_DEST)/`basename $$i`; done)

clean:
	rm -f *.cmi *.cmo *.ml.d *.mli.d jscoqtop.byte jscoqtop.js coqtop.byte coqtop.js
	rm -rf filesys

# Local stuff
upload: all
	cp -a index.html jscoqtop.js filesys/ css/ ~/x80/rhino-coq/


pau:
	rsync -avpz ~/research/jscoq pau:~/
	rsync -avpz pau:~/jscoq/ ~/research/pau-jscoq/

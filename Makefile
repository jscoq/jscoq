.PHONY: clean upload

# COQDIR=../coq-git/
COQDIR=/home/egallego/external/coq-git/

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
	ocamlfind ocamlc $(BYTEFLAGS) -linkall -linkpkg -thread -verbose -I +camlp5 -package unix -package camlp5 -package js_of_ocaml.tyxml dynlink.cma str.cma gramlib.cma $(COQDEPS) jscoq.cmo jscoqtop.cmo -o jscoqtop.byte

# JSFILES=mutex.js unix.js coq_vm.js aux.js
JSDIR=js
# JSFILES=$(JSDIR)/mutex.js $(JSDIR)/unix.js $(JSDIR)/coq_vm.js $(JSDIR)/ml_aux.js
JSFILES=$(JSDIR)/mutex.js $(JSDIR)/unix.js $(JSDIR)/coq_vm.js

# JSLIBFILES=nsp.js
# jscoqtop.js: jscoqtop.byte $(JSFILES) $(JSLIBFILES)

JSOO_OPTS=--pretty --noinline --disable shortvar

# --toplevel includes the linking information.
jscoqtop.js: jscoqtop.byte $(JSFILES)
	js_of_ocaml $(JSOO_OPTS) --toplevel --nocmis +nat.js +weak.js +toplevel.js $(JSFILES) jscoqtop.byte

COQTOP=$(COQDIR)/bin/coqtop.byte
NODEFILES=$(JSDIR)/fsInput.js

coqtop.byte: $(COQTOP)
	cp $(COQTOP) ./

coqtop.js: coqtop.byte jscoqtop.js $(JSFILES) $(NODEFILES)
	js_of_ocaml $(JSOO_OPTS) +nat.js +weak.js +toplevel.js $(JSFILES) $(NODEFILES) coqtop.byte

# print_cmo: print_cmo.ml
# 	ocamlc.opt -I /home/egallego/external/js_of_ocaml/compiler print_cmo.ml -o print_cmo

upload: all
	cp -a index.html jscoqtop.js readme.txt /home/egallego/x80/rhino-coq/

clean:
	rm -f *.cmi *.cmo *.ml.d *.mli.d jscoqtop.byte jscoqtop.js coqtop.byte coqtop.js

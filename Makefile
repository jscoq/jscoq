.PHONY: clean upload

# COQDIR=../coq-git/
COQDIR=/home/egallego/external/coq-git/

all: jscoqtop.js

# Include coq files
INCLUDETOP=-I $(COQDIR)/library/ -I $(COQDIR)/stm/ -I $(COQDIR)/lib/ -I $(COQDIR)/parsing/ -I $(COQDIR)/printing/ -I $(COQDIR)/kernel/ -I $(COQDIR)/proofs/

jscoq.cmi: jscoq.mli
	ocamlc -c -rectypes $(INCLUDETOP) jscoq.mli

jscoq.cmo: jscoq.cmi jscoq.ml
	ocamlc -c -rectypes $(INCLUDETOP) jscoq.ml

jscoqtop.cmo: jscoq.cmi
	ocamlfind ocamlc -c -syntax camlp4o -package bytes -package js_of_ocaml.syntax,lwt,js_of_ocaml.tyxml,js_of_ocaml.toplevel -package base64 -I camlp4 -package ocp-indent.lib -package higlo.ocaml -rectypes jscoqtop.ml

COQDEPS=$(COQDIR)/lib/clib.cma $(COQDIR)/lib/lib.cma $(COQDIR)/kernel/byterun/dllcoqrun.so $(COQDIR)/kernel/kernel.cma $(COQDIR)/library/library.cma $(COQDIR)/engine/engine.cma $(COQDIR)/pretyping/pretyping.cma $(COQDIR)/interp/interp.cma $(COQDIR)/proofs/proofs.cma $(COQDIR)/parsing/parsing.cma $(COQDIR)/printing/printing.cma $(COQDIR)/tactics/tactics.cma $(COQDIR)/stm/stm.cma $(COQDIR)/toplevel/toplevel.cma $(COQDIR)/parsing/highparsing.cma $(COQDIR)/tactics/hightactics.cma

jscoqtop.byte: $(COQDEPS) jscoq.cmo jscoqtop.cmo
	ocamlfind ocamlc -linkall -linkpkg -thread -verbose -I +camlp5 -package js_of_ocaml.tyxml -rectypes unix.cma threads.cma dynlink.cma str.cma gramlib.cma $(COQDEPS) jscoq.cmo jscoqtop.cmo -o jscoqtop.byte

# JSFILES=mutex.js unix.js coq_vm.js aux.js
JSFILES=mutex.js unix.js coq_vm.js

jscoqtop.js: jscoqtop.byte $(JSFILES)
	js_of_ocaml +nat.js +weak.js +toplevel.js $(JSFILES) jscoqtop.byte

COQTOP=$(COQDIR)/bin/coqtop.byte
NODEFILES=fsInput.js

coqtop.byte: $(COQTOP)
	cp $(COQTOP) ./

coqtop.js: coqtop.byte $(JSFILES) $(NODEFILES)
	js_of_ocaml +nat.js +weak.js +toplevel.js $(JSFILES) $(NODEFILES) coqtop.byte

upload: all
	cp -a index.html jscoqtop.js readme.txt /home/egallego/x80/rhino-coq/

clean:
	rm -f *.cmi *.cmo *.ml.d *.mli.d jscoqtop.byte jscoqtop.js coqtop.byte coqtop.js

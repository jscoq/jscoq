.PHONY: clean all

all: jscoqtop.js

# CAMLDEBUG=-g
CAMLDEBUG=
BYTEFLAGS=-rectypes -safe-string $(CAMLDEBUG)

JSOOFLAGS=-syntax camlp4o -package js_of_ocaml.syntax,js_of_ocaml.tyxml

# Our OCAML rules, we could refine the includes
%.cmi: %.mli
	ocamlfind ocamlc -c $(BYTEFLAGS) $(INCLUDETOP) $(JSOOFLAGS) $<

%.cmo: %.ml
	ocamlfind ocamlc -c $(BYTEFLAGS) $(INCLUDETOP) $(JSOOFLAGS) $<

########################################################################
# Main jscoq files
jscoqtop.byte: jscoqtop.cmo
	ocamlfind ocamlc $(BYTEFLAGS) -linkall -linkpkg -thread		\
	   -verbose $(JSOOFLAGS) -package camlp5 jscoqtop.cmo -o jscoqtop.byte

########################################################################
# Compilation to JS

# JSOO_OPTS=--pretty --noinline --disable shortvar --debug-info
# JSOO_OPTS=-opt 3
JSOO_OPTS=

JSDIR=../lib-js
JSFILES=$(JSDIR)/mutex.js

jscoqtop.js: jscoqtop.byte
	js_of_ocaml $(JSOO_OPTS) +nat.js +weak.js +dynlink.js +toplevel.js $(JSFILES) jscoqtop.byte

clean:
	rm -f *.cmi *.cmo *.ml.d *.mli.d jscoqtop.{byte,js}

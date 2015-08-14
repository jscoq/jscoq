.PHONY: clean all

all: jsoo_dl.js

# CAMLDEBUG=-g
CAMLDEBUG=
BYTEFLAGS=-rectypes -safe-string $(CAMLDEBUG)

JSOOFLAGS=-syntax camlp4o -package js_of_ocaml.syntax,js_of_ocaml.tyxml
JSOOFLAGS+=-package yojson,js_of_ocaml.compiler,js_of_ocaml.toplevel

# Our OCAML rules, we could refine the includes
%.cmi: %.mli
	ocamlfind ocamlc -c $(BYTEFLAGS) $(INCLUDETOP) $(JSOOFLAGS) $<

%.cmo: %.ml
	ocamlfind ocamlc -c $(BYTEFLAGS) $(INCLUDETOP) $(JSOOFLAGS) $<

########################################################################
# Main files

# -linkall is delicate here due the way js_of_ocaml works.
jsoo_dl.byte: jsoo_dl.cmo
	ocamlfind ocamlc $(BYTEFLAGS) -linkall -linkpkg -thread -verbose \
	   $(JSOOFLAGS) -package camlp5                                  \
	   dynlink.cma str.cma gramlib.cma jsoo_dl.cmo -o jsoo_dl.byte

########################################################################
# Compilation to JS

JSDIR=../lib-js
JSFILES=$(JSDIR)/mutex.js

# JSOO_OPTS=--pretty --noinline --disable shortvar --debug-info
# JSOO_OPTS=-opt 3
JSOO_OPTS=

# --toplevel includes the linking information.
jsoo_dl.js: jsoo_dl.byte $(JSFILES)
	js_of_ocaml $(JSOO_OPTS) --toplevel --nocmis +nat.js +weak.js +dynlink.js +toplevel.js $(JSFILES) jsoo_dl.byte

clean:
	rm -f *.cmi *.cmo *.ml.d *.mli.d jsoo_dl.byte jsoo_dl.js

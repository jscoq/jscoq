.PHONY: clean all

# CAMLDEBUG=-g
CAMLDEBUG=
BYTEFLAGS=-rectypes -safe-string $(CAMLDEBUG) -package yojson -I ../coq-js/

# Our OCAML rules, we could refine the includes
%.cmi: %.mli
	ocamlfind ocamlc -c $(BYTEFLAGS) $<

%.cmo: %.ml
	ocamlfind ocamlc -c $(BYTEFLAGS) $<

all: mklibfs mklibjson

COQ_LIB:=../coq-js/jslib.cmo

########################################################################
# Tools
mklibfs.cmo: $(COQ_LIB) dftlibs.cmo

mklibfs: mklibfs.cmo
	ocamlfind ocamlc $(BYTEFLAGS) $(COQ_LIB) dftlibs.cmo mklibfs.cmo -o mklibfs

mklibjson.cmo: $(COQ_LIB) dftlibs.cmo

mklibjson: mklibjson.cmo
	ocamlfind ocamlc $(BYTEFLAGS) -linkpkg -package yojson $(COQ_LIB) dftlibs.cmo mklibjson.cmo -o mklibjson

clean:
	rm -f *.cmi *.cmo *.ml.d *.mli.d mklibfs mklibjson

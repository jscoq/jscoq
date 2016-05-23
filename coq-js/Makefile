.PHONY: clean all jscoq32 jscoq64

include ../config.mk

# Empty default auction
all:

# Include coq files
INCLUDETOP=-I $(COQDIR)/library/   \
           -I $(COQDIR)/stm/       \
           -I $(COQDIR)/lib/       \
           -I $(COQDIR)/parsing/   \
           -I $(COQDIR)/printing/  \
           -I $(COQDIR)/kernel/    \
           -I $(COQDIR)/intf/      \
           -I $(COQDIR)/interp/    \
           -I $(COQDIR)/proofs/    \
           -I $(COQDIR)/toplevel   \
           -I $(COQDIR)/config

CAMLDEBUG=
# CAMLDEBUG=-g
CAMLWARN=-w @a-44-45
BYTEFLAGS=-rectypes -safe-string $(CAMLDEBUG) $(CAMLWARN)

JSOOFLAGS=-syntax camlp4o -package js_of_ocaml.syntax,js_of_ocaml.tyxml,compiler-libs,yojson

SEXPFLAGS=-package sexplib,ppx_sexp_conv

YOJSONFLAGS=

# Disabled for 4.03
# YOJSONFLAGS=-package yojson,ppx_deriving_yojson

# Our OCAML rules, we could refine the includes
%.cmi: %.mli
	ocamlfind ocamlc -c $(BYTEFLAGS) $(INCLUDETOP) $(JSOOFLAGS) $<

%.cmo: %.ml
	ocamlfind ocamlc -c $(BYTEFLAGS) $(INCLUDETOP) $(JSOOFLAGS) $<

########################################################################
# Main jscoq files
jslib.cmo: jslib.cmi
icoq.cmo: icoq.cmi

# 32-bit build
libmngstub.o: libmngstub.c
	gcc -m32 -c -o libmngstub.o libmngstub.c

jslibmng.cmo: icoq.cmo jslib.cmo libmngstub.o jslibmng.cmi

# Due to ppx auto-generated code.
JSWOVR=-w -4-39
jssexp.cmo: jssexp.ml
	ocamlfind ocamlc -c $(BYTEFLAGS) $(INCLUDETOP) $(SEXPFLAGS) $(YOJSONFLAGS) $(JSWOVR) $<

# PPXJSOO=-package ppx_deriving,js_of_ocaml.ppx
# jsjson.cmo: jsjson.ml
# 	ocamlfind ocamlc -c $(BYTEFLAGS) $(INCLUDETOP) $(PPXJSON) $<

# Main file
jscoq.cmi: jslibmng.cmi
jscoq.cmo: icoq.cmo jslibmng.cmo jssexp.cmo jscoq.cmi

COQDEPS=$(COQDIR)/lib/clib.cma			\
	$(COQDIR)/lib/lib.cma			\
	$(COQDIR)/kernel/byterun/dllcoqrun.so	\
	$(COQDIR)/kernel/kernel.cma		\
	$(COQDIR)/library/library.cma		\
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
	# For 8.6
	# $(COQDIR)/engine/engine.cma		\

# Enable/disable the dynlink hack (this bundles the whole jsoo compiler so it is heavy)
DL_HACK=yes

ifeq "${DL_HACK}" "yes"
JSOO_DL=jsoo_dl.cmo
endif

ifeq "${DL_HACK}" "no"
JSOO_DL=jsoo_cache.cmo
endif

ifeq "${JSOO_DL}" "jsoo_dl.cmo"
# JSOOFLAGS += -package js_of_ocaml.compiler,js_of_ocaml.toplevel
JSOOFLAGS += -package js_of_ocaml.compiler,compiler-libs.bytecomp
endif
# XXX: Why do we need to include compiler-libs.toplevel?...
# -package compiler-libs.common,compiler-libs.bytecomp,compiler-libs.toplevel

# We need to override due to
# "/home/egallego/external/coq-git/lib/lib.cma(Errors) and
#  /home/egallego/.opam/4.02.3+32bit/lib/ocaml/compiler-libs/ocamlbytecomp.cma(Errors)"
WOVR=-w -31

# -linkall is necessary, otherwise internal Coq tables are dropped:
#  Syntax error: entry [vernac:Vernac.vernac] is empty.
jscoq.byte: $(COQDEPS) jscoq.cmo $(JSOO_DL)
	ocamlfind ocamlc $(BYTEFLAGS) $(WOVR) -linkall -linkpkg -thread -verbose          \
	   $(JSOOFLAGS) -package camlp5,camlp5.gramlib,dynlink,sexplib,str                \
	   -custom -cclib libmngstub.o -cclib $(COQDIR)/kernel/byterun/dllcoqrun.so       \
	   $(COQDEPS) jslib.cmo icoq.cmo jslibmng.cmo jssexp.cmo $(JSOO_DL) jscoq.cmo -o jscoq.byte

jscoq32: jscoq.byte

########################################################################
# Compilation to JS

# JSFILES=mutex.js unix.js coq_vm.js aux.js
JSDIR=../lib-js
JSFILES=$(JSDIR)/mutex.js $(JSDIR)/unix.js $(JSDIR)/coq_vm.js $(JSDIR)/byte_cache.js

# JSLIBFILES=nsp.js
# jscoq.js: jscoq.byte $(JSFILES) $(JSLIBFILES)

JSOO_OPT_OPTS=
# JSOO_OPT_OPTS=--pretty --noinline --disable shortvar --debug-info
# JSOO_OPT_OPTS=-opt 3

# the --toplevel option is crutial to include the linking information
# and avoid "bytecode corrupted" messages from dynlink
JSOO_OPTS=--toplevel --nocmis $(JSOO_OPT_OPTS)

jscoq.js: jscoq.byte $(JSFILES)
	js_of_ocaml $(JSOO_OPTS) +nat.js +weak.js +dynlink.js +toplevel.js $(JSFILES) jscoq.byte

# For when we remove dyncomp
# js_of_ocaml $(JSOO_OPTS) +nat.js +weak.js +dynlink.js +toplevel.js $(JSFILES) jscoq.byte
# js_of_ocaml $(JSOO_OPTS) --toplevel --nocmis +nat.js +weak.js +dynlink.js +toplevel.js $(JSFILES) jscoq.byte

jscoq64: jscoq.js

clean:
	rm -f *.cmi *.cmo *.cma *.cmt *.cmti *.o *.ml.d *.mli.d jscoq.byte jscoq.js

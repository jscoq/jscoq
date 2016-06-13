.PHONY: clean all jscoq32 jscoq64

include ../config.mk

########################################################################
# jsCoq specific options                                               #
########################################################################

# Enable/disable the dynlink hack (this bundles the whole jsoo compiler so it is heavy)
JSCOQ_DL_HACK=yes

# Enable/disable debug compilation
JSCOQ_DEBUG=no

# Empty default auction
all:

# Include coq files
INCLUDETOP=-I $(COQDIR)/library/   \
           -I $(COQDIR)/stm/       \
           -I $(COQDIR)/engine/    \
           -I $(COQDIR)/pretying/  \
           -I $(COQDIR)/lib/       \
           -I $(COQDIR)/parsing/   \
           -I $(COQDIR)/grammar/   \
           -I $(COQDIR)/printing/  \
           -I $(COQDIR)/kernel/    \
           -I $(COQDIR)/intf/      \
           -I $(COQDIR)/interp/    \
           -I $(COQDIR)/proofs/    \
           -I $(COQDIR)/toplevel   \
           -I $(COQDIR)/config

CAMLDEBUG=

ifeq "${JSCOQ_DEBUG}" "yes"
CAMLDEBUG+=-g
endif

CAMLWARN=-w @a-44-45
BYTEFLAGS=-rectypes -safe-string $(CAMLDEBUG) $(CAMLWARN)

JSOOFLAGS=-syntax camlp4o -package js_of_ocaml.syntax,js_of_ocaml.tyxml,compiler-libs,yojson

SEXPFLAGS  = -package sexplib,ppx_sexp_conv
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

jslibmng.cmo: icoq.cmo jslib.cmo jslibmng.cmi

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
	$(COQDIR)/engine/engine.cma	        \
	$(COQDIR)/pretyping/pretyping.cma	\
	$(COQDIR)/interp/interp.cma		\
	$(COQDIR)/parsing/parsing.cma		\
	$(COQDIR)/grammar/grammar.cma		\
	$(COQDIR)/proofs/proofs.cma		\
	$(COQDIR)/printing/printing.cma		\
	$(COQDIR)/tactics/tactics.cma		\
	$(COQDIR)/stm/stm.cma			\
	$(COQDIR)/toplevel/toplevel.cma		\
	$(COQDIR)/parsing/highparsing.cma       \
	$(COQDIR)/ltac/ltac.cma

ifeq "${JSCOQ_DL_HACK}" "yes"
JSOO_DL=jsoo_dl.cmo
endif

ifeq "${JSCOQ_DL_HACK}" "no"
JSOO_DL=jsoo_cache.cmo
endif

# If we don't include compiler-libs.{bytecomp,toplevel}? we get an
# error at dynlink time:
#
# "Anomaly: "Assert_failure parse_bytecode.ml:619:2". Please report."
#
# We need to investigate more.
ifeq "${JSOO_DL}" "jsoo_dl.cmo"
# JSOOFLAGS += -package js_of_ocaml.compiler,js_of_ocaml.toplevel
JSOOFLAGS += -package js_of_ocaml.compiler,compiler-libs.common,compiler-libs.bytecomp,compiler-libs.toplevel
endif
# XXX: Why do we need to include compiler-libs.toplevel?...
# -package compiler-libs.common,compiler-libs.bytecomp,compiler-libs.toplevel

# We need to override due to
# "/home/egallego/external/coq-git/lib/lib.cma(Errors) and
#  /home/egallego/.opam/4.02.3+32bit/lib/ocaml/compiler-libs/ocamlbytecomp.cma(Errors)"
WOVR=-w -31

CAMLPD= $(shell ocamlfind query camlp5)/odyl.cma \
	$(shell ocamlfind query camlp5)/camlp5.cma

# -linkall is necessary, otherwise internal Coq tables are dropped:
#  Syntax error: entry [vernac:Vernac.vernac] is empty.
jscoq.byte: $(COQDEPS) jscoq.cmo $(JSOO_DL)
	ocamlfind ocamlc $(BYTEFLAGS) $(WOVR) -linkall -linkpkg -thread -verbose          \
	   $(JSOOFLAGS) -package camlp5,camlp5.gramlib,dynlink,sexplib,str                \
	   $(CAMLPD) \
	   $(COQDEPS) jslib.cmo icoq.cmo jslibmng.cmo jssexp.cmo $(JSOO_DL) jscoq.cmo -o jscoq.byte

jscoq32: jscoq.byte

########################################################################
# Compilation to JS

# JSFILES=mutex.js unix.js coq_vm.js aux.js
JSDIR=../lib-js
JSFILES=$(JSDIR)/mutex.js $(JSDIR)/unix.js $(JSDIR)/coq_vm.js $(JSDIR)/byte_cache.js

# JSLIBFILES=nsp.js
# jscoq.js: jscoq.byte $(JSFILES) $(JSLIBFILES)

# the --toplevel option is crutial to include the linking information
# and avoid "bytecode corrupted" messages from dynlink
JSOO_OPTS =--toplevel --nocmis

ifeq "${JSCOQ_DEBUG}" "yes"
JSOO_OPTS+= --pretty --noinline --disable shortvar --debug-info
endif
# JSOO_OPT_OPTS=--pretty --noinline --disable shortvar --debug-info
# JSOO_OPT_OPTS=-opt 3

jscoq.js: jscoq.byte $(JSFILES)
	js_of_ocaml $(JSOO_OPTS) +nat.js +weak.js +dynlink.js +toplevel.js $(JSFILES) jscoq.byte

# For when we remove dyncomp
# js_of_ocaml $(JSOO_OPTS) +nat.js +weak.js +dynlink.js +toplevel.js $(JSFILES) jscoq.byte
# js_of_ocaml $(JSOO_OPTS) --toplevel --nocmis +nat.js +weak.js +dynlink.js +toplevel.js $(JSFILES) jscoq.byte

jscoq64: jscoq.js

clean:
	$(RM) *.cmi *.cmo *.cma *.cmt *.cmti *.o *.ml.d *.mli.d jscoq.byte jscoq.js

.PHONY: clean all jscoq32 jscoq64

include ../config.mk

########################################################################
# jsCoq specific options                                               #
########################################################################

# Enable/disable debug compilation
JSCOQ_DEBUG=no

# Empty default auction
all:

# Include coq files
COQINCLUDE=-I $(COQDIR)/config     \
	   -I $(COQDIR)/clib/      \
	   -I $(COQDIR)/lib/       \
           -I $(COQDIR)/kernel/    \
           -I $(COQDIR)/library/   \
           -I $(COQDIR)/engine/    \
           -I $(COQDIR)/pretying/  \
           -I $(COQDIR)/interp/    \
           -I $(COQDIR)/parsing/   \
           -I $(COQDIR)/grammar/   \
           -I $(COQDIR)/printing/  \
           -I $(COQDIR)/intf/      \
           -I $(COQDIR)/proofs/    \
           -I $(COQDIR)/tactics/   \
           -I $(COQDIR)/vernac/    \
           -I $(COQDIR)/stm/

COQOBJS=$(COQDIR)/clib/clib.cma			\
	$(COQDIR)/lib/lib.cma			\
	$(COQDIR)/intf/intf.cma			\
	$(COQDIR)/kernel/kernel.cma		\
	$(COQDIR)/library/library.cma		\
	$(COQDIR)/engine/engine.cma	        \
	$(COQDIR)/pretyping/pretyping.cma	\
	$(COQDIR)/interp/interp.cma		\
	$(COQDIR)/proofs/proofs.cma		\
	$(COQDIR)/parsing/parsing.cma		\
	$(COQDIR)/printing/printing.cma		\
	$(COQDIR)/tactics/tactics.cma		\
	$(COQDIR)/vernac/vernac.cma		\
	$(COQDIR)/stm/stm.cma

CAMLDEBUG=

ifeq "${JSCOQ_DEBUG}" "yes"
CAMLDEBUG+=-g
endif

CAMLWARN=-w @a-39-44-45
BYTEFLAGS=-rectypes -safe-string $(CAMLDEBUG) $(CAMLWARN)

JSOOFLAGS=-package js_of_ocaml-ppx,js_of_ocaml-lwt,yojson,ppx_deriving_yojson

# Our OCAML rules, we could refine the includes
%.cmi: %.mli
	ocamlfind ocamlc -c $(BYTEFLAGS) $(COQINCLUDE) $(JSOOFLAGS) $<

%.cmo: %.ml
	ocamlfind ocamlc -c $(BYTEFLAGS) $(COQINCLUDE) $(JSOOFLAGS) $<

########################################################################
# Main jscoq files
jslib.cmo: jslib.cmi
icoq.cmo: icoq.cmi

jslibmng.cmo: icoq.cmo jslib.cmo jslibmng.cmi

# Main file
jscoq.cmi: jslibmng.cmi
jscoq.cmo: icoq.cmo jslibmng.cmo jscoq.cmi

# We need to override due to
# "/home/egallego/external/coq-git/lib/lib.cma(Errors) and
#  /home/egallego/.opam/4.02.3+32bit/lib/ocaml/compiler-libs/ocamlbytecomp.cma(Errors)"
WOVR=-w -31

# -linkall is necessary, otherwise internal Coq tables are dropped:
#  Syntax error: entry [vernac:Vernac.vernac] is empty.
# having to set CAML_LD_LIBRARY_PATH here is strange...
jscoq.byte: $(COQDEPS) jscoq.cmo
	CAML_LD_LIBRARY_PATH=$(COQDIR)/kernel/byterun:$(CAML_LD_LIBRARY_PATH) \
	ocamlfind ocamlc $(BYTEFLAGS) $(WOVR) -linkall -linkpkg -thread -verbose  \
	   -package str,dynlink,threads,camlp5,camlp5.gramlib                     \
	   $(JSOOFLAGS) $(COQOBJS)                                                \
           +nums.cma jslib.cmo icoq.cmo jslibmng.cmo jscoq.cmo -o jscoq.byte

jscoq32: jscoq.byte

########################################################################
# Compilation to JS

JSDIR=../coq-libjs/
JSFILES=$(addprefix $(JSDIR),mutex.js unix.js str.js coq_vm.js)

# the --toplevel was previously used, but --dynlink option seems to
# work equally fine, which one should we use? What about --nocmis,
# does it have any effect without --toplevel?
JSOO_OPTS = --dynlink # --nocmis

ifeq "${JSCOQ_DEBUG}" "yes"
JSOO_OPTS+= --pretty --noinline --disable shortvar --debug-info
endif

# No significant effect appreciated
# JSOO_OPTS+=-opt 3

jscoq.js: jscoq.byte $(JSFILES)
	js_of_ocaml $(JSOO_OPTS) +nat.js +dynlink.js +toplevel.js $(JSFILES) jscoq.byte

jscoq64: jscoq.js

clean:
	$(RM) *.cmi *.cmo *.cma *.cmt *.cmti *.o *.ml.d *.mli.d jscoq.byte jscoq.js

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
           -I $(COQDIR)/proofs/    \
           -I $(COQDIR)/tactics/   \
           -I $(COQDIR)/vernac/    \
           -I $(COQDIR)/stm/

COQOBJS=$(COQDIR)/clib/clib.cma			\
	$(COQDIR)/lib/lib.cma			\
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

CAMLWARN=-w @a-39-42-44-45
BYTEFLAGS=-rectypes -safe-string $(CAMLDEBUG) $(CAMLWARN)

# We use different compile/link flags.
JSOOCFLAGS=-package js_of_ocaml-ppx,js_of_ocaml-lwt,yojson,ppx_import,ppx_deriving_yojson
JSOOLFLAGS=-package js_of_ocaml-ppx,js_of_ocaml-lwt,yojson,ppx_deriving_yojson

ifeq "${shell uname -s}" "Darwin"
# On macOS, ocamlc invokes gcc, which then complains about missing symbols from libcoqrun.
JSOOLFLAGS+=-cclib "-undefined dynamic_lookup"
endif

# Our OCAML rules, we could refine the includes
%.cmi: %.mli
	ocamlfind ocamlc -c $(BYTEFLAGS) $(COQINCLUDE) $(JSOOCFLAGS) $<

%.cmo: %.ml
	ocamlfind ocamlc -c $(BYTEFLAGS) $(COQINCLUDE) $(JSOOCFLAGS) $<

########################################################################
# Main jscoq files
jslib.cmo: jslib.cmi
icoq.cmo: icoq.cmi

jslibmng.cmi: jslib.cmi
jslibmng.cmo: icoq.cmo jslib.cmo jslibmng.cmi
jscoq_doc.cmo: jscoq_doc.cmi

# Main file
jscoq_worker.cmo: jser_feedback.cmo jslibmng.cmo jscoq_doc.cmo

# We need to override due to
# "/home/egallego/external/coq-git/lib/lib.cma(Errors) and
#  /home/egallego/.opam/4.02.3+32bit/lib/ocaml/compiler-libs/ocamlbytecomp.cma(Errors)"
WOVR=-w -31

# -linkall is necessary, otherwise internal Coq tables are dropped:
#  Syntax error: entry [vernac:Vernac.vernac] is empty.
# having to set CAML_LD_LIBRARY_PATH here is strange...
jscoq_worker.byte: $(COQDEPS) jscoq_worker.cmo
	CAML_LD_LIBRARY_PATH=$(COQDIR)/kernel/byterun:$(CAML_LD_LIBRARY_PATH) \
	ocamlfind ocamlc $(BYTEFLAGS) $(WOVR) -linkall -linkpkg -thread -verbose  \
	   -package str,dynlink,threads,camlp5,camlp5.gramlib                     \
	   $(JSOOLFLAGS) $(COQOBJS)                                               \
           +nums.cma jslib.cmo icoq.cmo jslibmng.cmo jscoq_doc.cmo jser_feedback.cmo jscoq_worker.cmo -o jscoq_worker.byte

jscoq32: jscoq_worker.byte

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

jscoq_worker.js: jscoq_worker.byte $(JSFILES)
	js_of_ocaml $(JSOO_OPTS) +nat.js +dynlink.js +toplevel.js $(JSFILES) jscoq_worker.byte

jscoq64: jscoq_worker.js

clean:
	$(RM) *.cmi *.cmo *.cma *.cmt *.cmti *.o *.ml.d *.mli.d jscoq_worker.byte jscoq_worker.js

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
COQINCLUDE=-I $(COQDIR)/library/   \
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

COQOBJS=$(COQDIR)/lib/clib.cma			\
	$(COQDIR)/lib/lib.cma			\
	$(COQDIR)/kernel/byterun/dllcoqrun.so	\
	$(COQDIR)/kernel/kernel.cma		\
	$(COQDIR)/library/library.cma		\
	$(COQDIR)/engine/engine.cma	        \
	$(COQDIR)/pretyping/pretyping.cma	\
	$(COQDIR)/interp/interp.cma		\
	$(COQDIR)/proofs/proofs.cma		\
	$(COQDIR)/parsing/parsing.cma		\
	$(COQDIR)/printing/printing.cma		\
	$(COQDIR)/tactics/tactics.cma		\
	$(COQDIR)/stm/stm.cma			\
	$(COQDIR)/toplevel/toplevel.cma		\
	$(COQDIR)/parsing/highparsing.cma       \
	$(COQDIR)/ltac/ltac.cma

CAMLDEBUG=

ifeq "${JSCOQ_DEBUG}" "yes"
CAMLDEBUG+=-g
endif

CAMLWARN=-w @a-44-45
BYTEFLAGS=-rectypes -safe-string $(CAMLDEBUG) $(CAMLWARN)

JSOOFLAGS=-package js_of_ocaml.ppx,yojson

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
jscoq.byte: $(COQDEPS) jscoq.cmo
	ocamlfind ocamlc $(BYTEFLAGS) $(WOVR) -linkall -linkpkg -thread -verbose  \
	   -package str,dynlink,threads,camlp5,camlp5.gramlib                     \
	   $(JSOOFLAGS) $(COQOBJS)                                                \
           jslib.cmo icoq.cmo jslibmng.cmo jscoq.cmo -o jscoq.byte

jscoq32: jscoq.byte

########################################################################
# Compilation to JS

JSDIR=../coq-libjs/
JSFILES=$(addprefix $(JSDIR),mutex.js unix.js coq_vm.js)

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
	js_of_ocaml $(JSOO_OPTS) +nat.js +weak.js +dynlink.js +toplevel.js $(JSFILES) jscoq.byte

jscoq64: jscoq.js

clean:
	$(RM) *.cmi *.cmo *.cma *.cmt *.cmti *.o *.ml.d *.mli.d jscoq.byte jscoq.js

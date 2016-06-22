.PHONY: clean upload all libs coq-tools jscoq32 jscoq64 dist dist-upload dist-release dist-hott force

include config.mk

all:

jscoq32:
	$(MAKE) -C coq-js jscoq32

jscoq64:
	$(MAKE) -C coq-js jscoq64

coq-tools:
	$(MAKE) -C coq-tools

########################################################################
# CMA building                                                         #
########################################################################

%.cma.js: %.cma
	js_of_ocaml --wrap-with-fun $< -o $<.js

%.cmo.js: %.cmo
	js_of_ocaml --wrap-with-fun $< -o $<.js

# XXX FIXME
# Compile all cmo/cma in coq-pkgs
plugin-list: force
	find coq-pkgs \( -name *.cma -or -name *.cmo \) -fprintf plugin-list "%p.js:\n"

# | cmp -s - $@ || tee plugin-list

plugin-comp: $(addsuffix .js,$(shell find coq-pkgs \( -name *.cma -or -name *.cmo \)))

########################################################################
# Library building                                                     #
########################################################################

coq-pkgs:
	mkdir -p coq-pkgs

# It depends on coq-tools, but coq-tools is linked with the 32bit thing...
Makefile.libs: coq-tools/mklibfs
	./coq-tools/mklibfs > Makefile.libs

# Build Coq libraries
coq-libs: Makefile.libs coq-pkgs
	COQDIR=$(COQDIR) make -f Makefile.libs libs-auto

# Build extra libraries
coq-addons: coq-pkgs
	COQDIR=$(COQDIR) make -f Makefile.addons $(ADDONS)

coq-all-libs: coq-libs coq-addons

# All the libraries + json generation
libs: coq-all-libs
	./coq-tools/mklibjson # $(ADDONS)

########################################################################
# Dists                                                                #
########################################################################

BUILDDIR=dist

DISTHTML=newide.html #mtac_tutorial.html
BUILDOBJ=index.html $(DISTHTML) coq-pkgs ui-js ui-css ui-images examples
DISTEXT=$(addprefix ui-external/,CodeMirror CodeMirror-TeX-input pace d3.min.js bootstrap.min.css)

dist: libs
	ln -sf newide.html index.html
	mkdir -p $(BUILDDIR)
        # Copy static files, XXX: minimize
	rsync -avp --delete --exclude='*~' --exclude='.git' --exclude='.jshintrc' --delete-excluded $(BUILDOBJ) $(BUILDDIR)
        # The monster
	mkdir -p $(BUILDDIR)/coq-js/
	cp -a coq-js/jscoq.js $(BUILDDIR)/coq-js/
        # Externals
	rsync -avp --delete --exclude='*~' --exclude='.git' --delete-excluded $(DISTEXT) $(BUILDDIR)/ui-external

BUILDDIR_HOTT=$(BUILDDIR)-hott

HOTT_FILES=hott-init.json hott.json HoTT
HOTT_SRC_FILES=$(addprefix $(BUILDDIR)/coq-pkgs/,$(HOTT_FILES))

dist-hott:
	rsync -ap $(BUILDDIR)/ $(BUILDDIR_HOTT)
	rm -rf $(BUILDDIR_HOTT)/coq-pkgs/*
	rsync -ap $(HOTT_SRC_FILES) $(BUILDDIR_HOTT)/coq-pkgs/
	rsync -ap $(HOTT_COQLIB) $(BUILDDIR_HOTT)/coq-pkgs/Coq
	rsync -ap $(BUILDDIR)/coq-pkgs/Coq/syntax $(BUILDDIR_HOTT)/coq-pkgs/Coq/
	cp -a newhott.html $(BUILDDIR_HOTT)/newide.html

########################################################################
# coqDoc Object
########################################################################


########################################################################
# Clean                                                                #
########################################################################

clean:
	$(MAKE) -C coq-js       clean
	$(MAKE) -C coq-tools    clean
	rm -f *.cmi *.cmo *.ml.d *.mli.d Makefile.libs index.html
	rm -rf coq-pkgs
	rm -rf $(BUILDDIR) $(BUILDDIR_HOTT)

########################################################################
# Local stuff and distributions
########################################################################

hott-upload: dist-hott
	rsync -avzp --delete dist-hott/ $(HOTT_RELEASE)

dist-upload: all
	rsync -avzp --delete dist/ $(WEB_DIR)

dist-release: all
	rsync -avzp --delete --exclude=README.md --exclude=get-hashes.sh --exclude=.git dist/ $(RELEASE_DIR)

# all-dist: dist dist-hott dist-release dist-upload hott-upload
all-dist: dist dist-release dist-upload

pau:
	rsync -avpz ~/research/jscoq pau:~/
	rsync -avpz pau:~/jscoq/ ~/research/pau-jscoq/

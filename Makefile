.PHONY: clean upload all libs coq-tools jscoq32 jscoq64 dist dist-upload dist-release dist-hott force coq coq-get coq-build dune-build

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
	js_of_ocaml --wrap-with-fun= -o $<.js $<

%.cmo.js: %.cmo
	js_of_ocaml --wrap-with-fun= -o $<.js $<

# XXX FIXME
# Compile all cmo/cma in coq-pkgs
plugin-list: coq-pkgs force
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
	ln -sf $(DISTHTML) index.html
	mkdir -p $(BUILDDIR)
        # Copy static files, XXX: minimize
	rsync -avp --delete --exclude='*~' --exclude='.git' --exclude='.jshintrc' --delete-excluded $(BUILDOBJ) $(BUILDDIR)
        # The monster
	mkdir -p $(BUILDDIR)/coq-js/
	cp -a coq-js/jscoq.js $(BUILDDIR)/coq-js/
        # Externals
	rsync -avp --delete --exclude='*~' --exclude='.git' --exclude='node_modules' --delete-excluded $(DISTEXT) $(BUILDDIR)/ui-external

BUILDDIR_HOTT=$(BUILDDIR)-hott

HOTT_FILES=hott-init.json hott.json HoTT
HOTT_SRC_FILES=$(addprefix $(BUILDDIR)/coq-pkgs/,$(HOTT_FILES))

dist-hott:
	rsync -av $(BUILDDIR)/ $(BUILDDIR_HOTT)
	rm -rf $(BUILDDIR_HOTT)/coq-pkgs/*
	rsync -av $(HOTT_SRC_FILES) $(BUILDDIR_HOTT)/coq-pkgs/
	rsync -av $(HOTT_COQLIB) $(BUILDDIR_HOTT)/coq-pkgs/Coq
	rsync -av $(BUILDDIR)/coq-pkgs/Coq/syntax $(BUILDDIR_HOTT)/coq-pkgs/Coq/
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

COQ_BRANCH=v8.9
COQ_REPOS=https://github.com/coq/coq.git
NJOBS=4

coq-get:
	mkdir -p coq-external coq-pkgs
	git clone --depth=1 -b $(COQ_BRANCH) $(COQ_REPOS) coq-external/coq-$(COQ_VERSION)+32bit || true
	cd coq-external/coq-$(COQ_VERSION)+32bit && ./configure -local -native-compiler no -bytecode-compiler no -coqide no
	make -f coq-addons/mathcomp.addon get
	make -f coq-addons/iris.addon get
#	make -f coq-addons/equations.addon get
	make -f coq-addons/ltac2.addon get
	make -f coq-addons/elpi.addon get
	make -f coq-addons/dsp.addon get

coq-build:
	cd coq-external/coq-$(COQ_VERSION)+32bit && make -j $(NJOBS) && make -j $(NJOBS) byte
	make -f coq-addons/mathcomp.addon build jscoq-install
	make -f coq-addons/iris.addon build jscoq-install
#	make -f coq-addons/equations.addon build jscoq-install
	make -f coq-addons/ltac2.addon build jscoq-install
	make -f coq-addons/elpi.addon build jscoq-install
	make -f coq-addons/dsp.addon jscoq-install

coq: coq-get coq-build

coq-js/jscoq.js: force
	OCAMLPATH=$(COQDIR) dune build --profile=release coq-js/jscoq.bc.js
	cp _build/default/coq-js/jscoq.bc.js coq-js/jscoq.js

dune-build: coq-js/jscoq.js

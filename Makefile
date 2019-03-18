.PHONY: all clean upload all libs coq-tools
.PHONY: bytecode_bin javascript_bin
.PHONY: dist dist-upload dist-release dist-hott force
.PHONY: coq coq-get coq-build

include config.mk

all:
	@echo "Welcome to jsCoq makefile. Targets are:"
	@echo ""
	@echo "  - bytecode_bin:   build jscoq's bytecode"
	@echo "  - javascript_bin: build jscoq's javascript"
	@echo "  - coq-get:        download Coq and libraries"
	@echo "  - coq-build:      build Coq and libraries"
	@echo "  - coq:            download and build Coq and libraries"
	@echo "  - coq-tools:      to be removed by the Dune-based build"

bytecode_bin:
	$(MAKE) -C coq-js bytecode_bin

javascript_bin:
	$(MAKE) -C coq-js javascript_bin

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

# Bundle libs and inject dependencies
libs-pkg:
	node coq-tools/mkpkg.js coq-pkgs/*.json
	node coq-tools/mkdeps.js coq-pkgs/init.json coq-pkgs/coq-*.json $(COQDIR)/.vfiles.d

########################################################################
# Dists                                                                #
########################################################################

BUILDDIR=dist

DISTHTML=newide.html #mtac_tutorial.html
BUILDOBJ=package.json index.html $(DISTHTML) coq-pkgs ui-js ui-css ui-images examples
DISTEXT=$(addprefix ui-external/,CodeMirror-TeX-input)

dist:
	ln -sf $(DISTHTML) index.html
	mkdir -p $(BUILDDIR)
	# Copy static files, XXX: minimize
	rsync -avp --delete --exclude='*~' --exclude='.git' --exclude='.jshintrc' --exclude='*.cmo' \
	      --delete-excluded $(BUILDOBJ) $(BUILDDIR)
	# The monster
	mkdir -p $(BUILDDIR)/coq-js/
	cp -a coq-js/jscoq.js coq-js/jscoq_worker.js $(BUILDDIR)/coq-js/
	# Externals
	rsync -avp --delete --exclude='*~' --exclude='.git' --exclude='node_modules' --delete-excluded $(DISTEXT) $(BUILDDIR)/ui-external
	# Node stuff
	cd $(BUILDDIR) && npm install

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

dist-upload: dist
	rsync -avzp --delete dist/ $(WEB_DIR)

dist-release: dist
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
	( git clone --depth=1 -b $(COQ_BRANCH) $(COQ_REPOS) $(COQDIR) && \
	  cd $(COQDIR) && \
          patch -p1 < $(current_dir)/coq-patches/avoid-vm.patch && \
          patch -p1 < $(current_dir)/coq-patches/trampoline.patch ) || true
	cd $(COQDIR) && ./configure -local -native-compiler no -bytecode-compiler no -coqide no
	make -f coq-addons/mathcomp.addon get
	make -f coq-addons/iris.addon get
	make -f coq-addons/equations.addon get
	make -f coq-addons/ltac2.addon get
	make -f coq-addons/elpi.addon get
	make -f coq-addons/dsp.addon get

COQ_TARGETS = theories plugins bin/coqc bin/coqtop bin/coqdep bin/coq_makefile
COQ_MAKE_FLAGS = -j $(NJOBS)

ifeq "${shell uname -s}" "Darwin"
# Coq cannot be built natively on macOS with 32-bit.
# At least not unless plugins are linked statically.
COQ_MAKE_FLAGS += BEST=byte
endif


coq-build:
	cd coq-external/coq-$(COQ_VERSION)+32bit && $(MAKE) $(COQ_TARGETS) $(COQ_MAKE_FLAGS) && $(MAKE) byte $(COQ_MAKE_FLAGS)
	make -f coq-addons/mathcomp.addon build jscoq-install
	make -f coq-addons/iris.addon build jscoq-install
	make -f coq-addons/equations.addon build jscoq-install
	make -f coq-addons/ltac2.addon build jscoq-install
	make -f coq-addons/elpi.addon build jscoq-install
	make -f coq-addons/dsp.addon build jscoq-install

coq: coq-get coq-build

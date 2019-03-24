.PHONY: all clean force
.PHONY: jscoq libs-pkg links links-clean
.PHONY: dist dist-upload dist-release

# Coq Version
COQ_VERSION:=v8.10
JSCOQ_BRANCH:=

JSCOQ_VERSION:=$(COQ_VERSION)

ifdef JSCOQ_BRANCH
JSCOQ_VERSION:=$(JSCOQ_VERSION)-$(JSCOQ_BRANCH)
endif

# ugly but I couldn't find a better way
current_dir := $(dir $(realpath $(lastword $(MAKEFILE_LIST))))

# Directory where the coq sources and developments are.
ADDONS_PATH := $(current_dir)/coq-external
COQDIR := coq-external/coq-$(COQ_VERSION)/

# Find where dune places coq build artifacts
_COQBUILDDIR = ${wildcard $(current_dir)/_build/*/$(COQDIR)}
COQBUILDDIR = ${if ${filter 1,${words $(_COQBUILDDIR)}}, $(_COQBUILDDIR), \
	${error error: exactly one Coq build should be active; found ${words $(_COQBUILDDIR)} [$(_COQBUILDDIR)]}}

# Find where dune places coq build artifacts
COQPKGDIR = ${patsubst %/$(COQDIR),%/coq-pkgs,$(COQBUILDDIR)}

NJOBS=4

export NJOBS
export COQDIR
export ADDONS_PATH

ADDONS = mathcomp # iris ltac2 elpi equations dsp

all:
	@echo "Welcome to jsCoq makefile. Targets are:"
	@echo ""
	@echo "     jscoq: build jscoq [javascript and libraries]"
	@echo "  libs-pkg: build packages bundle [experimental]"
	@echo ""
	@echo "     links: create links that allow to serve pages from the source tree"
	@echo ""
	@echo "      dist: create a distribution suitable for a web server"
	@echo "       coq: download and build Coq and addon libraries"

jscoq: force
	ADDONS="$(ADDONS)" OCAMLPATH=$(COQDIR) \
        dune build @jscoq

libs-pkg: force
	ADDONS="$(ADDONS)" OCAMLPATH=$(COQDIR) \
	dune build @libs-pkg

links:
	ln -sf ${wildcard _build/*/coq-pkgs/} . || true
	ln -sf ../${wildcard _build/*/coq-js/jscoq_worker.bc.js} coq-js || true

links-clean:
	rm coq-pkgs coq-js/jscoq_worker.bc.js

########################################################################
# Clean                                                                #
########################################################################

clean:
	dune clean

########################################################################
# Dists                                                                #
########################################################################

BUILDDIR=_build/default
BUILDOBJ=$(addprefix $(BUILDDIR)/./, index.html node_modules coq-js/jscoq_worker.bc.js coq-pkgs ui-js ui-css ui-images examples ui-external/CodeMirror-TeX-input)
DISTDIR=_build/dist

dist: jscoq
	mkdir -p $(DISTDIR)
	rsync -avpR --delete $(BUILDOBJ) $(DISTDIR)

########################################################################
# Local stuff and distributions
########################################################################

# Private paths, for releases and local builds.
WEB_DIR=~/x80/jscoq-builds/$(JSCOQ_VERSION)/
RELEASE_DIR=~/research/jscoq-builds/

dist-upload: dist
	rsync -avzp --delete $(DISTDIR)/ $(WEB_DIR)

dist-release: dist
	rsync -avzp --delete --exclude=README.md --exclude=get-hashes.sh --exclude=.git $(DISTDIR)/ $(RELEASE_DIR)

# all-dist: dist dist-release dist-upload
all-dist: dist dist-release dist-upload

########################################################################
# External's
########################################################################

.PHONY: coq coq-get coq-build

COQ_BRANCH=master
COQ_REPOS=https://github.com/coq/coq.git

coq-get:
	mkdir -p coq-external coq-pkgs
	( git clone --depth=1 -b $(COQ_BRANCH) $(COQ_REPOS) $(COQDIR) && \
	  cd $(COQDIR) && \
          patch -p1 < $(current_dir)/etc/patches/avoid-vm.patch && \
          patch -p1 < $(current_dir)/etc/patches/trampoline.patch && \
		  patch -p1 < $(current_dir)/etc/patches/coerce-32bit.patch ) || true
	cd $(COQDIR) && ./configure -local -native-compiler no -bytecode-compiler no -coqide no
	for i in $(ADDONS); do make -f coq-addons/$$i.addon get; done

COQ_TARGETS = theories plugins bin/coqc bin/coqtop bin/coqdep bin/coq_makefile
COQ_MAKE_FLAGS = -j $(NJOBS)

ifeq "${shell uname -s}" "Darwin"
# Coq cannot be built natively on macOS with 32-bit.
# At least not unless plugins are linked statically.
COQ_MAKE_FLAGS += BEST=byte
endif

coq-build:
	./build-theories.sh
	# cd coq-external/coq-$(COQ_VERSION)+32bit && $(MAKE) $(COQ_TARGETS) $(COQ_MAKE_FLAGS) && $(MAKE) byte $(COQ_MAKE_FLAGS)
	# COQDIR=/home/egallego/research/jscoq/_build/install/4.07.1+32bit 

addons-build:
	@printf 'Using Coq from:\n - %s\n\n' '$(COQBUILDDIR)'
	@printf 'Installing to:\n - %s\n\n' '$(COQPKGDIR)'
	for i in $(ADDONS); do make -f coq-addons/$$i.addon build jscoq-install COQDIR=$(COQBUILDDIR); done
	rsync -va coq-pkgs/ $(COQPKGDIR)/

coq: coq-get coq-build

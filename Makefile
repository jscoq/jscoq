.PHONY: all clean force
.PHONY: jscoq libs-pkg links links-clean
.PHONY: dist dist-upload dist-release

-include ./config.inc

# Coq Version
COQ_VERSION:=v8.10
JSCOQ_BRANCH:=

JSCOQ_VERSION:=$(COQ_VERSION)

ifdef JSCOQ_BRANCH
JSCOQ_VERSION:=$(JSCOQ_VERSION)-$(JSCOQ_BRANCH)
endif

WORD_SIZE ?= 32

ifeq ($(WORD_SIZE),64)
BUILD_CONTEXT = default
DUNE_WORKSPACE = $(current_dir)/dune-workspace-64
else
BUILD_CONTEXT = 4.07.1+32bit
VARIANT = +32bit
endif

# ugly but I couldn't find a better way
current_dir := $(dir $(realpath $(lastword $(MAKEFILE_LIST))))

# Directory where the Coq sources and developments are.
ADDONS_PATH := $(current_dir)/coq-external
COQSRC := $(ADDONS_PATH)/coq-$(COQ_VERSION)$(VARIANT)/

# Directories where Dune builds and installs Coq
COQBUILDDIR := $(current_dir)/_build/$(BUILD_CONTEXT)/coq-external/coq-$(COQ_VERSION)$(VARIANT)
COQDIR := $(current_dir)/_build/install/$(BUILD_CONTEXT)

DUNE_FLAGS := ${if $(DUNE_WORKSPACE), --workspace=$(DUNE_WORKSPACE),}

NJOBS=4

export NJOBS
export COQDIR
export COQBUILDDIR
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
	ADDONS="$(ADDONS)" dune build @jscoq $(DUNE_FLAGS)

libs-pkg: force
	ADDONS="$(ADDONS)" dune build @libs-pkg $(DUNE_FLAGS)

links:
	ln -sf _build/$(BUILD_CONTEXT)/coq-pkgs .
	ln -sf ../_build/$(BUILD_CONTEXT)/coq-js/jscoq_worker.js coq-js

links-clean:
	rm -f coq-pkgs coq-js/jscoq_worker.js

# Build symbol database files for autocomplete
coq-pkgs/%.symb: coq-pkgs/%.json
	node --max-old-space-size=2048 ui-js/coq-cli.js --require-pkg $< --inspect $@

libs-symb: ${patsubst %.json, %.symb, coq-pkgs/init.json ${wildcard coq-pkgs/coq-*.json}}

########################################################################
# Clean                                                                #
########################################################################

clean:
	dune clean

########################################################################
# Dists                                                                #
########################################################################

BUILDDIR=_build/$(BUILD_CONTEXT)
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
# Externals
########################################################################

.PHONY: coq coq-get coq-build

COQ_BRANCH=v8.10
COQ_REPOS=https://github.com/coq/coq.git

COQ_PATCHES = trampoline lazy-noinline

ifeq ($(WORD_SIZE),64)
	COQ_PATCHES += coerce-32bit
endif

ifeq (${shell uname}/$(WORD_SIZE),Darwin/32)
	COQ_PATCHES += byte-only
endif

$(COQSRC):
	mkdir -p coq-external
	git clone --depth=1 -b $(COQ_BRANCH) $(COQ_REPOS) $@
	cd $@ && git apply ${foreach p,$(COQ_PATCHES),$(current_dir)/etc/patches/$p.patch}

coq-get: $(COQSRC)
	cd $(COQSRC) && ./configure -prefix $(COQDIR) -native-compiler no -bytecode-compiler no -coqide no
	dune build @vodeps $(DUNE_FLAGS)
	cd $(COQSRC) && dune exec ./tools/coq_dune.exe $(DUNE_FLAGS) --context="$(BUILD_CONTEXT)" $(COQBUILDDIR)/.vfiles.d

# Coq should be now be built by composition with the Dune setup
coq-build:
	true

coq: coq-get coq-build

addon-%-get:
	make -f coq-addons/$*.addon get

addon-%-build:
	make -f coq-addons/$*.addon build
	make -f coq-addons/$*.addon jscoq-install

addons-get: ${foreach v,$(ADDONS),addon-$(v)-get}
addons-build: ${foreach v,$(ADDONS),addon-$(v)-build}

addons: addons-get addons-build

.PHONY: all clean force
.PHONY: jscoq jscoq_worker libs-pkg links links-clean
.PHONY: dist dist-upload dist-release

-include ./config.inc

# Coq Version
COQ_VERSION:=v8.11
JSCOQ_BRANCH:=

JSCOQ_VERSION:=$(COQ_VERSION)

ifdef JSCOQ_BRANCH
JSCOQ_VERSION:=$(JSCOQ_VERSION)-$(JSCOQ_BRANCH)
endif

WORD_SIZE ?= 32
OS := ${shell uname}
ARCH := $(OS)/$(WORD_SIZE)

ifeq ($(WORD_SIZE),64)
DUNE_WORKSPACE = $(current_dir)/dune-workspace-64
VARIANT = +64bit
else
VARIANT = +32bit
endif

BUILD_CONTEXT = jscoq$(VARIANT)

# ugly but I couldn't find a better way
current_dir := $(dir $(realpath $(lastword $(MAKEFILE_LIST))))

# Directory where the Coq sources and developments are.
ADDONS_PATH := $(current_dir)/_vendor+$(COQ_VERSION)$(VARIANT)
COQSRC := $(ADDONS_PATH)/coq/

# Directories where Dune builds and installs Coq
COQBUILDDIR_REL := _vendor+$(COQ_VERSION)$(VARIANT)/coq
COQBUILDDIR := $(current_dir)/_build/$(BUILD_CONTEXT)/$(COQBUILDDIR_REL)
COQDIR := $(current_dir)/_build/install/$(BUILD_CONTEXT)

COQPKGS_ROOT := $(current_dir)/_build/$(BUILD_CONTEXT)/coq-pkgs

DUNE_FLAGS := ${if $(DUNE_WORKSPACE), --workspace=$(DUNE_WORKSPACE),}

NJOBS=4

export NJOBS
export BUILD_CONTEXT

export COQDIR
export COQBUILDDIR
export COQBUILDDIR_REL
export ADDONS_PATH
export COQPKGS_ROOT

ADDONS = mathcomp # elpi equations dsp # iris

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

jscoq_worker:
	ADDONS="$(ADDONS)" dune build @jscoq_worker $(DUNE_FLAGS)

libs-pkg: force
	ADDONS="$(ADDONS)" dune build @libs-pkg $(DUNE_FLAGS) --force

links:
	ln -sf _build/$(BUILD_CONTEXT)/coq-pkgs .
	ln -sf ../_build/$(BUILD_CONTEXT)/coq-js/jscoq_worker.bc.js coq-js/jscoq_worker.js
#	ln -sf ../_build/$(BUILD_CONTEXT)/ui-js/coq-build.browser.js ui-js

links-clean:
	rm -f coq-pkgs coq-js/jscoq_worker.js
#	ui-js/coq-build.browser.js

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
BUILDOBJ=${addprefix $(BUILDDIR)/./, \
	index.html coq-js/jscoq_worker.bc.js \
	coq-pkgs ui-js ui-css ui-images examples \
	node_modules ui-external/CodeMirror-TeX-input}
DISTDIR=_build/dist
STAGEDIR=_build/staging

PACKAGE_VERSION = ${shell node -p 'require("./package.json").version'}

dist: jscoq libs-pkg
	mkdir -p $(DISTDIR)
	rsync -avpR --delete README.md $(BUILDOBJ) $(DISTDIR)

TAREXCLUDE = --exclude node_modules --exclude '*.vo' --exclude '*.cma'

dist-tarball: dist
	# Hack to make the tar contain a jscoq-x.x directory
	rm -f _build/jscoq-$(PACKAGE_VERSION)
	ln -fs dist _build/jscoq-$(PACKAGE_VERSION)
	tar zcf /tmp/jscoq-$(PACKAGE_VERSION).tar.gz   \
	    -C _build $(TAREXCLUDE) --exclude '*.bak' --exclude '*.tar.gz' \
	    --dereference jscoq-$(PACKAGE_VERSION)
	mv /tmp/jscoq-$(PACKAGE_VERSION).tar.gz $(DISTDIR)

NPMOBJ = ${filter-out %/node_modules %/index.html, $(BUILDOBJ)}
NPMOBJ += README.md package.json package-lock.json
NPMEXCLUDE = --delete-excluded --exclude '*.vo' --exclude '*.cma'

dist-npm:
	mkdir -p $(STAGEDIR) $(DISTDIR)
	rsync -avpR --delete $(NPMEXCLUDE) $(NPMOBJ) $(STAGEDIR)
	cp docs/npm-landing.html $(STAGEDIR)/index.html
	sed -i.bak 's/\(is_npm:\) false/\1 true/' $(STAGEDIR)/ui-js/jscoq-loader.js
	tar zcf $(DISTDIR)/jscoq-$(PACKAGE_VERSION)-npm.tar.gz   \
	    -C $(STAGEDIR) --exclude '*.bak' .

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

COQ_BRANCH=v8.11
COQ_REPOS=https://github.com/coq/coq.git

COQ_PATCHES = trampoline cps timeout $(COQ_PATCHES|$(WORD_SIZE)) $(COQ_PATCHES|$(ARCH))

COQ_PATCHES|64 = coerce-32bit
COQ_PATCHES|Darwin/32 = byte-only

$(COQSRC):
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
#	make -f coq-addons/$*.addon jscoq-install

addons-get: ${foreach v,$(ADDONS),addon-$(v)-get}
addons-build: ${foreach v,$(ADDONS),addon-$(v)-build}

addons: addons-get addons-build

test:
	npx mocha tests/main.js

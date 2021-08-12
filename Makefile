.PHONY: all clean force
.PHONY: jscoq jscoq_worker links links-clean
.PHONY: dist dist-upload dist-release server

-include ./config.inc

# Coq Version
COQ_VERSION := v8.13
JSCOQ_BRANCH :=

JSCOQ_VERSION := $(COQ_VERSION)

ifdef JSCOQ_BRANCH
JSCOQ_VERSION:=$(JSCOQ_VERSION)-$(JSCOQ_BRANCH)
endif

WORD_SIZE ?= 32
OS := ${shell uname}
ARCH := $(OS)/$(WORD_SIZE)

ifeq ($(WORD_SIZE),64)
DUNE_WORKSPACE = $(current_dir)/dune-workspace.64
VARIANT = +64bit
else
VARIANT = +32bit
endif

BUILD_CONTEXT = jscoq$(VARIANT)
BUILDDIR = _build/$(BUILD_CONTEXT)

OPAMENV = eval `opam env --set-switch --switch $(BUILD_CONTEXT)`
DUNE = $(OPAMENV) && dune

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

override DUNE_FLAGS += ${if $(DUNE_WORKSPACE), --workspace=$(DUNE_WORKSPACE),}

NJOBS ?= 4

export NJOBS
export BUILD_CONTEXT

export COQDIR
export COQBUILDDIR
export COQBUILDDIR_REL
export ADDONS_PATH
export COQPKGS_ROOT

ifdef DEBUG
JSCOQ_DEBUG = 1
export JSCOQ_DEBUG
endif

all:
	@echo "Welcome to jsCoq makefile. Targets are:"
	@echo ""
	@echo "     jscoq: build jsCoq [JavaScript and libraries]"
	@echo "     wacoq: build waCoq [JavaScript, frontend only; depends on wacoq-bin]"
	@echo ""
	@echo "     links: create links that allow to serve pages from the source tree"
	@echo ""
	@echo "      dist: create a distribution suitable for a web server"
	@echo "  dist-npm: create NPM packages suitable for `npm install`"
	@echo "       coq: download and build Coq and addon libraries"
	@echo "   install: install Coq version used by jsCoq to ~/.opam/$(BUILD_CONTEXT)"

jscoq: force
	$(DUNE) build @jscoq $(DUNE_FLAGS)

jscoq_worker:
	$(DUNE) build @jscoq_worker $(DUNE_FLAGS)

install:
	$(DUNE) build -p coq $(DUNE_FLAGS)
	$(DUNE) install coq $(DUNE_FLAGS)

links:
	ln -sf _build/$(BUILD_CONTEXT)/coq-pkgs .
	ln -sf ../_build/$(BUILD_CONTEXT)/coq-js/jscoq_worker.bc.js coq-js/jscoq_worker.js

links-clean:
	rm -f coq-pkgs coq-js/jscoq_worker.js

# Build symbol database files for autocomplete
coq-pkgs/%.symb: coq-pkgs/%.json
	node --max-old-space-size=2048 ui-js/coq-cli.js --require-pkg $< --inspect $@

libs-symb: ${patsubst %.json, %.symb, coq-pkgs/init.json ${wildcard coq-pkgs/coq-*.json}}

wacoq:
	# Currently, this builds in the source tree
	[ -d node_modules ] || npm install
	npm run build

########################################################################
# Developer Zone                                                       #
########################################################################

.PHONY: test watch serve dev

test:
	npx mocha tests/main.js

watch: DUNE_FLAGS+=--watch
watch: jscoq

serve:
	npx http-server $(BUILDDIR) -p 8013 -c 0

dev:
	$(MAKE) serve &
	$(MAKE) watch

########################################################################
# Clean                                                                #
########################################################################

clean:
	$(DUNE) clean
	rm -f jscoq-*.tar.gz

distclean: clean
	rm -rf $(COQSRC)

########################################################################
# Dists                                                                #
########################################################################

BUILDOBJ = ${addprefix $(BUILDDIR)/./, \
	coq-js/jscoq_worker.bc.js coq-pkgs \
	ui-js ui-css ui-images ui-external examples dist}
DISTOBJ = README.md index.html package.json package-lock.json $(BUILDOBJ)
DISTDIR = _build/dist

PACKAGE_VERSION = ${shell node -p 'require("./package.json").version'}

dist: jscoq
	mkdir -p $(DISTDIR)
	rsync -apR --delete $(DISTOBJ) $(DISTDIR)

TAREXCLUDE = --exclude assets --exclude '*.cma' \
	--exclude '*.bak' --exclude '*.tar.gz' \
    ${foreach dir, Coq Ltac2 mathcomp, \
		--exclude '${dir}/**/*.vo' --exclude '${dir}/**/*.cma.js'}

dist-tarball: dist
	# Hack to make the tar contain a jscoq-x.x directory
	@rm -f _build/jscoq-$(PACKAGE_VERSION)
	ln -fs dist _build/jscoq-$(PACKAGE_VERSION)
	tar zcf /tmp/jscoq-$(PACKAGE_VERSION).tar.gz -C _build $(TAREXCLUDE) \
	    --dereference jscoq-$(PACKAGE_VERSION)
	mv /tmp/jscoq-$(PACKAGE_VERSION).tar.gz $(DISTDIR)
	@rm -f _build/jscoq-$(PACKAGE_VERSION)

NPMOBJ = ${filter-out index.html package-lock.json, $(DISTOBJ)}
NPMSTAGEDIR = _build/package
NPMEXCLUDE = --delete-excluded --exclude assets

dist-npm:
	mkdir -p $(NPMSTAGEDIR) $(DISTDIR)
	rsync -apR --delete $(NPMEXCLUDE) $(NPMOBJ) $(NPMSTAGEDIR)
	cp docs/npm-landing.html $(NPMSTAGEDIR)/index.html
	npm pack ./$(NPMSTAGEDIR)

WACOQ_NPMOBJ = README.md \
	ui-js ui-css ui-images ui-external examples dist
# ^ plus `package.json` and `docs/npm-landing.html` that have separate treatment	

dist-npm-wacoq:
	mkdir -p $(NPMSTAGEDIR) $(DISTDIR)
	rm -rf ${add-prefix $(NPMSTAGEDIR)/, coq-js coq-pkgs}  # in case these were created by jsCoq :/
	rsync -apR --delete $(NPMEXCLUDE) $(NPMOBJ) $(NPMSTAGEDIR)
	cp package.json.wacoq $(NPMSTAGEDIR)/package.json
	cp docs/npm-landing.html $(NPMSTAGEDIR)/index.html
	npm pack ./$(NPMSTAGEDIR)

# The need to maintain and update `package.json.wacoq` alongside `package.json`
# is absolutely bothersome. I could not conjure a more sustainable way to emit
# two separate NPM packages from the same source tree, though.

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

.PHONY: coq coq-get coq-get-latest coq-build

COQ_BRANCH = V8.13.2
COQ_BRANCH_LATEST = v8.13
COQ_REPOS = https://github.com/coq/coq.git

COQ_PATCHES = trampoline fold timeout $(COQ_PATCHES|$(WORD_SIZE)) $(COQ_PATCHES|$(ARCH))

COQ_PATCHES|64 = coerce-32bit
COQ_PATCHES|Darwin/32 = byte-only

$(COQSRC):
	git -c advice.detachedHead=false clone --depth=1 -b $(COQ_BRANCH) $(COQ_REPOS) $@
	cd $@ && git apply ${foreach p,$(COQ_PATCHES),$(current_dir)/etc/patches/$p.patch}

coq-get: $(COQSRC)
	$(OPAMENV) && \
	cd $(COQSRC) && ./configure -prefix $(COQDIR) -native-compiler no -bytecode-compiler no -coqide no

coq-get-latest: COQ_BRANCH = $(COQ_BRANCH_LATEST)
coq-get-latest: coq-get

coq: coq-get

# - These are deprecated (use jscoq/addons repo instead)

addon-%-get:
	make -f coq-addons/$*.addon get

addon-%-build:
	make -f coq-addons/$*.addon build

addons-get: ${foreach v,$(ADDONS),addon-$(v)-get}
addons-build: ${foreach v,$(ADDONS),addon-$(v)-build}

addons: addons-get addons-build

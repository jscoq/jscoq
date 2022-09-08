.PHONY: all clean force
.PHONY: jscoq jscoq_worker links links-clean
.PHONY: dist dist-upload dist-release serve

-include ./config.inc

# Coq Version
COQ_VERSION := v8.16
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
VENDOR_PATH := $(current_dir)/_vendor+$(COQ_VERSION)$(VARIANT)
COQSRC := $(VENDOR_PATH)/coq/

# Directories where Dune builds and installs Coq
COQBUILDDIR_REL := _vendor+$(COQ_VERSION)$(VARIANT)/coq
COQBUILDDIR := $(current_dir)/_build/$(BUILD_CONTEXT)/$(COQBUILDDIR_REL)
COQDIR := $(current_dir)/_build/install/$(BUILD_CONTEXT)
# Dune packages to install for Coq
COQINST := coq coq-core coq-stdlib
COQINST_COMMAS = $(subst $(space),$(comma),$(COQINST))

COQPKGS_ROOT := $(current_dir)/_build/$(BUILD_CONTEXT)/coq-pkgs

override DUNE_FLAGS += ${if $(DUNE_WORKSPACE), --workspace=$(DUNE_WORKSPACE),}

NJOBS ?= 4

export NJOBS
export BUILD_CONTEXT

export COQDIR
export COQBUILDDIR
export COQBUILDDIR_REL
export COQPKGS_ROOT

ifdef DEBUG
JSCOQ_DEBUG = 1
export JSCOQ_DEBUG
endif

null  :=
space := $(null) #
comma := ,

all:
	@echo "Welcome to jsCoq makefile. Targets are:"
	@echo ""
	@echo "     jscoq: build jsCoq [JavaScript and libraries]"
	@echo "     wacoq: build waCoq [JavaScript, frontend only; depends on wacoq-bin]"
	@echo ""
	@echo "     links: create links that allow to serve pages from the source tree"
	@echo ""
	@echo "      dist: create a distribution suitable for a web server"
	@echo "  dist-npm: create NPM packages suitable for \`npm install\`"
	@echo "       coq: download and build Coq and addon libraries"
	@echo "   install: install Coq version used by jsCoq to ~/.opam/$(BUILD_CONTEXT)"

jscoq: force
	$(DUNE) build @jscoq $(DUNE_FLAGS)

coq-pkgs: force
	$(DUNE) build coq-pkgs $(DUNE_FLAGS)

jscoq_worker:
	$(DUNE) build @jscoq_worker $(DUNE_FLAGS)

install:
	$(DUNE) build -p $(COQINST_COMMAS) $(DUNE_FLAGS)
	$(DUNE) install $(COQINST) $(DUNE_FLAGS)

links:
	ln -sf _build/$(BUILD_CONTEXT)/coq-pkgs .
	ln -sf ../_build/$(BUILD_CONTEXT)/coq-js/jscoq_worker.bc.cjs coq-js/jscoq_worker.bc.cjs

links-clean:
	rm -f coq-pkgs coq-js/jscoq_worker.bc.cjs

# Build symbol database files for autocomplete
coq-pkgs/%.symb.json: coq-pkgs/%.coq-pkg
	node --max-old-space-size=2048 ./dist/cli.cjs run --require-pkg $* --inspect $@

libs-symb: ${patsubst %.coq-pkg, %.symb.json, ${wildcard coq-pkgs/*.coq-pkg}}

wacoq:
	# Currently, this builds in the source tree
	[ -d node_modules ] || npm install
	rm -rf dist
	npm run build

########################################################################
# Developer Zone                                                       #
########################################################################

.PHONY: test watch serve dev

test:
	$(DUNE) exec --context=$(BUILD_CONTEXT) $(DUNE_FLAGS) -- npx mocha tests/main.js

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
	rm -f jscoq-*.tgz

distclean: clean
	rm -rf $(COQSRC)

########################################################################
# Dists                                                                #
########################################################################

BUILDOBJ = ${addprefix $(BUILDDIR)/./, \
	coq-js/jscoq_worker.bc.cjs coq-pkgs \
	jscoq.js ui-js ui-css ui-images ui-external dist examples}
DISTOBJ = README.md index.html package.json package-lock.json $(BUILDOBJ)
DISTDIR = _build/dist

PACKAGE_VERSION = ${shell node -p 'require("./package.json").version'}

dist: jscoq
	mkdir -p $(DISTDIR)
	rsync -apR --delete $(DISTOBJ) $(DISTDIR)

TAREXCLUDE = --exclude assets --exclude '*.cma' \
	--exclude '*.bak' --exclude '*.tgz' \
    ${foreach dir, Coq Ltac2 mathcomp, \
		--exclude '${dir}/**/*.vo' --exclude '${dir}/**/*.cma.js'}

dist-tarball: dist
	# Hack to make the tar contain a jscoq-x.x directory
	@rm -f _build/jscoq-$(PACKAGE_VERSION)
	ln -fs dist _build/jscoq-$(PACKAGE_VERSION)
	tar zcf /tmp/jscoq-$(PACKAGE_VERSION).tgz -C _build $(TAREXCLUDE) \
	    --dereference jscoq-$(PACKAGE_VERSION)
	mv /tmp/jscoq-$(PACKAGE_VERSION).tgz $(DISTDIR)
	@rm -f _build/jscoq-$(PACKAGE_VERSION)

NPMOBJ = ${filter-out index.html package-lock.json, $(DISTOBJ)}
NPMSTAGEDIR = _build/package
NPMEXCLUDE = --delete-excluded --exclude assets --exclude _build

dist-npm:
	mkdir -p $(NPMSTAGEDIR) $(DISTDIR)
	rsync -apR --delete $(NPMEXCLUDE) $(NPMOBJ) $(NPMSTAGEDIR)
	cp docs/npm-landing.html $(NPMSTAGEDIR)/index.html
	mv /tmp/$$( cd /tmp && npm pack $(PWD)/$(NPMSTAGEDIR) | tail -1 ) \
		$(DISTDIR)/jscoq-$(PACKAGE_VERSION)-npm.tgz
	@echo $(DISTDIR)/jscoq-$(PACKAGE_VERSION)-npm.tgz

WACOQ_NPMOBJ = README.md \
	jscoq.js ui-js ui-css ui-images ui-external examples dist
# ^ plus `package.json` and `docs/npm-landing.html` that have separate treatment

dist-npm-wacoq:
	mkdir -p $(NPMSTAGEDIR) $(DISTDIR)
	rm -rf ${add-prefix $(NPMSTAGEDIR)/, coq-js coq-pkgs}  # in case these were created by jsCoq :/
	rsync -apR --delete $(NPMEXCLUDE) $(WACOQ_NPMOBJ) $(NPMSTAGEDIR)
	cp package.json.wacoq $(NPMSTAGEDIR)/package.json
	cp docs/npm-landing.html $(NPMSTAGEDIR)/index.html
	npm pack ./$(NPMSTAGEDIR)

# The need to maintain and update `package.json.wacoq` alongside `package.json`
# is absolutely bothersome. I could not conjure a more sustainable way to emit
# two separate NPM packages from the same source tree, though.

########################################################################
# Externals
########################################################################

.PHONY: coq coq-get coq-get-latest coq-build

COQ_BRANCH = V8.16.0
COQ_BRANCH_LATEST = v8.16
COQ_REPOS = https://github.com/coq/coq.git

COQ_PATCHES = trampoline fold timeout $(COQ_PATCHES|$(WORD_SIZE)) $(COQ_PATCHES|$(ARCH))

COQ_PATCHES|64 = coerce-32bit

$(COQSRC):
	git -c advice.detachedHead=false clone --depth=1 -b $(COQ_BRANCH) $(COQ_REPOS) $@
	cd $@ && git apply ${foreach p,$(COQ_PATCHES),$(current_dir)/etc/patches/$p.patch}

coq_configure=./tools/configure/configure.exe

coq-get: $(COQSRC)
	$(OPAMENV) && \
	cd $(COQSRC) && dune exec $(DUNE_FLAGS) $(coq_configure) --context=$(BUILD_CONTEXT) -- -prefix $(COQDIR) -native-compiler no -bytecode-compiler no -coqide no

coq-get-latest: COQ_BRANCH = $(COQ_BRANCH_LATEST)
coq-get-latest: coq-get

coq: coq-get

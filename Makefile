.PHONY: all clean force
.PHONY: jscoq jscoq-static jscoq_worker links links-clean
.PHONY: dist serve

-include ./config.inc

# Coq Version
COQ_VERSION := v8.20
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

# This is very convenient when calling npm, a bit less when compiling
# OCaml code
DUNE_FLAGS=--no-buffer
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
	@echo "     wacoq: build waCoq [JavaScript and libraries]"
	@echo ""
	@echo "    bundle: create the core JS bundles using esbuild in dist"
	@echo " typecheck: typecheck using tsc"
	@echo "   release: create the core JS bundles using release mode"
	@echo ""
	@echo "     links: create links that allow to serve pages from the source tree"
	@echo "            [note: jscoq build system auto-promotoes targets so this is obsolete]"
	@echo ""
	@echo "      dist: create a distribution suitable for a web server"
	@echo "  dist-npm: create NPM packages suitable for \`npm install\`"
	@echo "       coq: download and build Coq and addon libraries"
	@echo "   install: install Coq version used by jsCoq to ~/.opam/$(BUILD_CONTEXT)"

jscoq-static: force
	$(DUNE) build @jscoq-static $(DUNE_FLAGS)

jscoq: force
	$(DUNE) build @jscoq $(DUNE_FLAGS)

wacoq: force
	$(DUNE) build @wacoq $(DUNE_FLAGS)

coq-pkgs: force
	$(DUNE) build coq-pkgs $(DUNE_FLAGS)

jscoq_worker:
	$(DUNE) build @jscoq_worker $(DUNE_FLAGS)

wacoq_worker:
	$(DUNE) build @wacoq_worker $(DUNE_FLAGS)

install:
	$(DUNE) build -p $(COQINST_COMMAS) $(DUNE_FLAGS)
	$(DUNE) install $(COQINST) $(DUNE_FLAGS)

links:
	ln -sf _build/$(BUILD_CONTEXT)/coq-pkgs .
	ln -sf ../../_build/$(BUILD_CONTEXT)/backend/jsoo/jscoq_worker.bc.js backend/jsoo/jscoq_worker.bc.js
	ln -sf ../../_build/$(BUILD_CONTEXT)/backend/wasm/wacoq_worker.bc backend/wasm/wacoq_worker.bc
	ln -sf ../../_build/$(BUILD_CONTEXT)/backend/wasm/dlllib_stubs.wasm backend/wasm/dlllib_stubs.wasm
	ln -sf ../../_build/$(BUILD_CONTEXT)/backend/wasm/dllcoqrun_stubs.wasm backend/wasm/dllcoqrun_stubs.wasm

links-clean:
	rm -f coq-pkgs backend/jsoo/jscoq_worker.bc.js backend/wasm/wacoq_worker.bc \
	       backend/wasm/dlllib_stubs.wasm backend/wasm/dllcoqrun_stubs.wasm

.PHONY:modules bundle typecheck bundle-webpack
modules:
	$(DUNE) build node_modules

bundle:
	$(DUNE) build dist dist-cli

bundle-webpack:
	$(DUNE) build dist-webpack --no-buffer

typecheck:
	$(DUNE) build node_modules
	$(DUNE) exec --context=$(BUILD_CONTEXT) -- npm run typecheck

release:
	JSCOQ_BUNDLE_TARGET=release $(DUNE) build dist
	JSCOQ_BUNDLE_TARGET=release-cli $(DUNE) build dist-cli

# Build symbol database files for autocomplete
coq-pkgs/%.symb.json: coq-pkgs/%.coq-pkg
	@node --max-old-space-size=2048 ./dist-cli/cli.cjs run --require-pkg $* --inspect $@

libs-symb: ${patsubst %.coq-pkg, %.symb.json, ${wildcard coq-pkgs/*.coq-pkg}}

########################################################################
# Developer Zone                                                       #
########################################################################

.PHONY: test watch serve dev

test:
	$(DUNE) exec --context=$(BUILD_CONTEXT) $(DUNE_FLAGS) -- npx mocha tests/main.js

watch: DUNE_FLAGS+=--watch
watch: jscoq

serve:
	npx serve -c ../../etc/serve.json -C -l 8013 $(BUILDDIR)

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

dist: dist-npm dist-tarball

# Emilio: Ideally we would like to remove frontend and backend from
# here once the dist directory is setup.
BUILDOBJ = ${addprefix $(BUILDDIR)/./,coq-pkgs frontend backend dist examples docs}
DISTOBJ = README.md index.html package.json package-lock.json $(BUILDOBJ)
DISTDIR = _build/dist

PACKAGE_VERSION = ${shell node -p 'require("./package.json").version'}

TAREXCLUDE = --exclude assets --exclude '*.cma' \
	--exclude '*.bak' --exclude '*.tgz' \
    ${foreach dir, Coq Ltac2 mathcomp, \
		--exclude '${dir}/**/*.vo' --exclude '${dir}/**/*.cma.js'}

dist-tarball:
	@echo
	mkdir -p $(DISTDIR)
	rsync -apR --delete $(DISTOBJ) $(DISTDIR)
	@# Hack to make the tar contain a jscoq-x.x directory
	@rm -f _build/jscoq-$(PACKAGE_VERSION)
	ln -fs dist _build/jscoq-$(PACKAGE_VERSION)
	tar zcf /tmp/jscoq-$(PACKAGE_VERSION)-dist.tgz -C _build $(TAREXCLUDE) \
	    --dereference jscoq-$(PACKAGE_VERSION)
	mv /tmp/jscoq-$(PACKAGE_VERSION)-dist.tgz $(DISTDIR)
	@rm -f _build/jscoq-$(PACKAGE_VERSION)
	@echo ">" $(DISTDIR)/jscoq-$(PACKAGE_VERSION)-dist.tgz

NPMOBJ = ${filter-out index.html package-lock.json, $(DISTOBJ)}
NPMSTAGEDIR = _build/package
NPMEXCLUDE = --delete-excluded --exclude assets --exclude _build

dist-npm:
	@echo
	mkdir -p $(NPMSTAGEDIR) $(DISTDIR)
	rsync -apR --delete $(NPMEXCLUDE) $(NPMOBJ) $(NPMSTAGEDIR)
	cp docs/npm-landing.html $(NPMSTAGEDIR)/index.html
	cd $(DISTDIR) && npm pack $(PWD)/$(NPMSTAGEDIR)
	@echo ">" $(DISTDIR)/jscoq-$(PACKAGE_VERSION).tgz

########################################################################
# Retrieving and Patching Coq source code
########################################################################

.PHONY: coq coq-get coq-get-latest coq-build

COQ_BRANCH = V8.20.0
COQ_BRANCH_LATEST = v8.20
COQ_REPOS = https://github.com/coq/coq.git

COQ_PATCHES = interrupt # trampoline fold timeout $(COQ_PATCHES|$(WORD_SIZE)) $(COQ_PATCHES|$(ARCH))

COQ_PATCHES|64 = coerce-32bit

$(COQSRC):
	git -c advice.detachedHead=false clone --depth=1 -b $(COQ_BRANCH) $(COQ_REPOS) $@
	cd $@ && git apply ${foreach p,$(COQ_PATCHES),$(current_dir)/etc/patches/$p.patch}

coq_configure=./tools/configure/configure.exe

coq-get: $(COQSRC)
	$(OPAMENV) && \
	cd $(COQSRC) && dune exec $(DUNE_FLAGS) $(coq_configure) --context=$(BUILD_CONTEXT) -- -prefix $(COQDIR) -native-compiler no -bytecode-compiler no
	# Temporarily re-enable Dune for libs (disabled in Coq 8.20)
	cd $(COQSRC) && cp theories/dune.disabled theories/dune
	cd $(COQSRC) && cp user-contrib/Ltac2/dune.disabled user-contrib/Ltac2/dune

coq-get-latest: COQ_BRANCH = $(COQ_BRANCH_LATEST)
coq-get-latest: coq-get

coq: coq-get

# Submodules setup

# Initialise submodules
.PHONY: submodules-init
submodules-init:
	git submodule update --init

# Deinitialize submodules
.PHONY: submodules-deinit
submodules-deinit:
	git submodule deinit -f --all

# Update submodules from upstream
.PHONY: submodules-update
submodules-update:
	(cd vendor/coq && git checkout master && git pull upstream master)

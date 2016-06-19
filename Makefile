.PHONY: clean upload all libs coq-tools jsoo-util jscoq32 jscoq64 bcache dist dist-upload dist-release dist-hott

include config.mk

all:

jscoq32:
	$(MAKE) -C coq-js jscoq32

jscoq64:
	$(MAKE) -C coq-js jscoq64

# Disabled for now
# jsoo-util:
# 	$(MAKE) -C jsoo-util

coq-tools:
	$(MAKE) -C coq-tools

########################################################################
# Library building                                                     #
########################################################################

coq-pkgs:
	mkdir -p coq-pkgs

# It depends on coq-tools, but coq-tools is linked with the 32bit thing...
Makefile.libs: coq-tools/dftlibs.ml coq-tools/mklibfs.ml
	./coq-tools/mklibfs > Makefile.libs

# Build Coq libraries
coq-libs: Makefile.libs
	COQDIR=$(COQDIR) make -f Makefile.libs libs-auto

# Build extra libraries
coq-addons:
	make -f Makefile.addons $(ADDONS)

# All the libraries + json generation
libs: coq-libs coq-addons coq-pkgs
	COQDIR=$(COQDIR) make -f Makefile.libs libs-auto
	./coq-tools/mklibjson # $(ADDONS)

# CMAS=filesys/Coq_syntax/nat_syntax_plugin.cma	\
#      filesys/Coq_cc/cc_plugin.cma		\
#      filesys/Coq_firstorder/ground_plugin.cma	\
#      filesys/Coq_decl_mode/decl_mode_plugin.cma

# %.cma.js: %.cma
# 	js_of_ocaml --toplevel --nocmis +nat.js +weak.js +dynlink.js	\
# 	+toplevel.js js/mutex.js js/unix.js js/coq_vm.js		\
# 	js/byte_cache.js jscoqtop.js $< -o filesys/cmas/$<.js

########################################################################
# bcache building                                                      #
########################################################################

bcache: coq-pkgs bcache.stamp

bcache.stamp: bc-md5.json bc-js.json # $(wildcard coq-fs/*/*.cma)
	mkdir -p coq-pkgs/bcache
	nodejs ./coq-tools/byte_cache.js > coq-pkgs/bcache.list
	ls coq-pkgs/bcache > coq-pkgs/bcache.list
	perl -i -pe "chomp if eof" coq-pkgs/bcache.list
	touch bcache.stamp

BUILDDIR=dist

DISTHTML=newide.html #mtac_tutorial.html
BUILDOBJ=index.html $(DISTHTML) js css images examples coq-pkgs
DISTEXT=external/CodeMirror external/CodeMirror-TeX-input external/pace external/d3.min.js external/bootstrap.min.css

# dist: bcache libs
dist: libs
	ln -sf newide.html index.html
	mkdir -p $(BUILDDIR)
        # Copy static files, XXX: minimize
	rsync -avp --delete --exclude='*~' --exclude='.git' --exclude='.jshintrc' --delete-excluded $(BUILDOBJ) $(BUILDDIR)
        # The monster
	mkdir -p $(BUILDDIR)/coq-js/
	cp -a coq-js/jscoq.js $(BUILDDIR)/coq-js/
        # Externals
	rsync -avp --delete --exclude='*~' --exclude='.git' --delete-excluded $(DISTEXT) $(BUILDDIR)/external

BUILDDIR_HOTT=$(BUILDDIR)-hott

HOTT_FILES=bcache bcache.list hott-init.json hott.json HoTT
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
# $(MAKE) -C jsoo-util clean
	rm -f *.cmi *.cmo *.ml.d *.mli.d Makefile.libs index.html
	rm -rf coq-pkgs
	rm -rf bcache.stamp bc-md5.json bc-js.json
	rm -rf $(BUILDDIR) $(BUILDDIR_HOTT)

########################################################################
# Local stuff and distributions
########################################################################

hott-upload: dist-hott
	rsync -avzp --delete dist-hott/ $(HOTT_RELEASE)

dist-upload: all #bcache
	rsync -avzp --delete dist/ $(WEB_DIR)

dist-release: all #bcache
	rsync -avzp --delete --exclude=README.md --exclude=get-hashes.sh --exclude=.git dist/ $(RELEASE_DIR)

# all-dist: dist dist-hott dist-release dist-upload hott-upload
all-dist: dist dist-release dist-upload

pau:
	rsync -avpz ~/research/jscoq pau:~/
	rsync -avpz pau:~/jscoq/ ~/research/pau-jscoq/

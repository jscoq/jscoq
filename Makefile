.PHONY: clean upload all libs coq-tools jsoo-util jscoq32 jscoq64 bcache build

COQDIR=~/external/coq-git/

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

coq-fs:
	mkdir -p coq-fs

coq-pkgs:
	mkdir -p coq-pkgs

Makefile.libs: coq-tools
	./coq-tools/mklibfs > Makefile.libs

# Build Coq libraries
coq-libs: Makefile.libs
	COQDIR=$(COQDIR) make -f Makefile.libs libs-auto

# Build extra libraries
coq-addons:
	make -f Makefile.addons all-addons

# All the libraries + json generation
libs: coq-libs coq-addons coq-pkgs
	COQDIR=$(COQDIR) make -f Makefile.libs libs-auto
	./coq-tools/mklibjson

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

bcache: bcache.stamp

bcache.stamp: bc-md5.json bc-js.json # $(wildcard coq-fs/*/*.cma)
	mkdir -p bcache
	nodejs ./coq-tools/byte_cache.js >> bcache.list
	touch bcache.stamp

BUILDDIR=dist

BUILDOBJ=index.html newide.html js css images coq-fs coq-pkgs bcache.list bcache
DISTEXT=external/CodeMirror external/pace external/d3.min.js external/bootstrap.min.css

dist: bcache libs
	ln -sf newide.html index.html
	mkdir -p $(BUILDDIR)
        # Copy static files, XXX: minimize
	rsync -avp --delete --exclude='*~' --exclude='.git' --exclude='.jshintrc' --delete-excluded $(BUILDOBJ) $(BUILDDIR)
        # The monster
	mkdir -p $(BUILDDIR)/coq-js/
	cp -a coq-js/jscoq.js $(BUILDDIR)/coq-js/
        # Externals
	rsync -avp --delete --exclude='*~' --exclude='.git' --delete-excluded $(DISTEXT) $(BUILDDIR)/external

########################################################################
# Clean                                                                #
########################################################################

clean:
	$(MAKE) -C coq-js       clean
	$(MAKE) -C coq-tools    clean
	$(MAKE) -C coq-toplevel clean
# $(MAKE) -C jsoo-util clean
	rm -f *.cmi *.cmo *.ml.d *.mli.d Makefile.libs index.html
	rm -rf coq-fs
	rm -rf coq-pkgs
	rm -rf bcache bcache.list bcache.stamp bc-md5.json bc-js.json
	rm -rf build

########################################################################
# Local stuff
########################################################################

dist-upload: all bcache
	rsync -avzp --delete dist/ ~/x80/rhino-coq/

dist-release: all bcache
	rsync -avzp --delete --exclude=README.md --exclude=get-hashes.sh --exclude=.git dist/ ~/research/jscoq-builds/

upload: all
	ln -sf newide.html index.html
	mkdir -p ~/x80/rhino-coq/coq-js/
	rsync -avzp coq-js/jscoq.js ~/x80/rhino-coq/coq-js/
	rsync --delete -avzp index.html newide.html ide.html js css images coq-fs coq-pkgs bcache.list bcache external ~/x80/rhino-coq/
# $(shell ./x80-sync.sh)

pau:
	rsync -avpz ~/research/jscoq pau:~/
	rsync -avpz pau:~/jscoq/ ~/research/pau-jscoq/

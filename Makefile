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
# Plugin building + base64 encoding

coq-fs:
	mkdir -p coq-fs

Makefile.libs: coq-tools
	./coq-tools/mklibfs > Makefile.libs

# Addons

SSR_HOME=~/external/coq/math-comp/mathcomp/

SSR_PLUG=$(SSR_HOME)/ssreflect.cma

SSR_DEST=coq-fs/mathcomp_ssreflect
SSR_FILES=$(wildcard $(SSR_HOME)/ssreflect/*.vo)

# XXX: Use a pattern rule!
$(SSR_DEST):
	mkdir -p $(SSR_DEST)

ssr: $(SSR_DEST) $(SSR_PLUG) $(SSR_FILES)
	$(shell cp -a $(SSR_PLUG) $(SSR_DEST)/ssreflect.cma)
	$(shell for i in $(SSR_FILES); do cp -a $$i $(SSR_DEST)/`basename $$i`; done)

SSR_ALG_DEST=coq-fs/mathcomp_algebra
SSR_ALG_FILES=$(wildcard $(SSR_HOME)/algebra/*.vo)

$(SSR_ALG_DEST):
	mkdir -p $(SSR_ALG_DEST)

ssr-alg: $(SSR_ALG_DEST) $(SSR_ALG_FILES)
	$(shell for i in $(SSR_ALG_FILES); do cp -a $$i $(SSR_ALG_DEST)/`basename $$i`; done)

SSR_FIN_DEST=coq-fs/mathcomp_fingroup
SSR_FIN_FILES=$(wildcard $(SSR_HOME)/fingroup/*.vo)

$(SSR_FIN_DEST):
	mkdir -p $(SSR_FIN_DEST)

ssr-fin: $(SSR_FIN_DEST) $(SSR_FIN_FILES)
	$(shell for i in $(SSR_FIN_FILES); do cp -a $$i $(SSR_FIN_DEST)/`basename $$i`; done)

SSR_SOL_DEST=coq-fs/mathcomp_solvable
SSR_SOL_FILES=$(wildcard $(SSR_HOME)/solvable/*.vo)

$(SSR_SOL_DEST):
	mkdir -p $(SSR_SOL_DEST)

ssr-sol: $(SSR_SOL_DEST) $(SSR_SOL_FILES)
	$(shell for i in $(SSR_SOL_FILES); do cp -a $$i $(SSR_SOL_DEST)/`basename $$i`; done)

SSR_FLD_DEST=coq-fs/mathcomp_field
SSR_FLD_FILES=$(wildcard $(SSR_HOME)/field/*.vo)

$(SSR_FLD_DEST):
	mkdir -p $(SSR_FLD_DEST)

ssr-fld: $(SSR_FLD_DEST) $(SSR_FLD_FILES)
	$(shell for i in $(SSR_FLD_FILES); do cp -a $$i $(SSR_FLD_DEST)/`basename $$i`; done)

lib-addons: ssr ssr-alg ssr-fin ssr-sol ssr-fld

libs: Makefile.libs lib-addons
	COQDIR=$(COQDIR) make -f Makefile.libs libs-auto
	./coq-tools/mklibjson > coq_pkg.json

# CMAS=filesys/Coq_syntax/nat_syntax_plugin.cma	\
#      filesys/Coq_cc/cc_plugin.cma		\
#      filesys/Coq_firstorder/ground_plugin.cma	\
#      filesys/Coq_decl_mode/decl_mode_plugin.cma

# %.cma.js: %.cma
# 	js_of_ocaml --toplevel --nocmis +nat.js +weak.js +dynlink.js	\
# 	+toplevel.js js/mutex.js js/unix.js js/coq_vm.js		\
# 	js/byte_cache.js jscoqtop.js $< -o filesys/cmas/$<.js

bcache: bcache.stamp

bcache.stamp: bc-md5.json bc-js.json # $(wildcard coq-fs/*/*.cma)
	mkdir -p bcache
	nodejs ./coq-tools/byte_cache.js > bcache.list
	touch bcache.stamp

BUILDDIR=dist

BUILDOBJ=index.html newide.html js css images coq_pkg.json coq-fs bcache.list bcache
DISTEXT=external/CodeMirror external/pace external/d3.min.js external/bootstrap.min.css

dist: bcache libs
	ln -sf newide.html index.html
	mkdir -p $(BUILDDIR)
        # Copy static files, XXX: minimize
	rsync -avp --delete --exclude='*~' --exclude='.git' --delete-excluded $(BUILDOBJ) $(BUILDDIR)
        # The monster
	mkdir -p $(BUILDDIR)/coq-js/
	cp -a coq-js/jscoq.js $(BUILDDIR)/coq-js/
        # Externals
	rsync -avp --delete --exclude='*~' --exclude='.git' --delete-excluded $(DISTEXT) $(BUILDDIR)/external

clean:
	$(MAKE) -C coq-js       clean
	$(MAKE) -C coq-tools    clean
	$(MAKE) -C coq-toplevel clean
# $(MAKE) -C jsoo-util clean
	rm -f *.cmi *.cmo *.ml.d *.mli.d Makefile.libs index.html
	rm -rf coq-fs
	rm -rf bcache bcache.list bc-md5.json bc-js.json
	rm -rf build


########################################################################
# Local stuff
dist-upload: all bcache
	rsync -avzp --delete dist/ ~/x80/rhino-coq/

upload: all
	ln -sf newide.html index.html
	mkdir -p ~/x80/rhino-coq/coq-js/
	rsync -avzp coq-js/jscoq.js ~/x80/rhino-coq/coq-js/
	rsync --delete -avzp index.html newide.html ide.html js css images coq-fs coq_pkg.json coq_pkg_aux.json bcache.list bcache external ~/x80/rhino-coq/
# $(shell ./x80-sync.sh)

pau:
	rsync -avpz ~/research/jscoq pau:~/
	rsync -avpz pau:~/jscoq/ ~/research/pau-jscoq/

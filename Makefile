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

# SSRDIR=~/external/coq/ssr-git/
# SSR_PLUG=$(SSRDIR)/src/ssreflect.cma
# SSR=$(SSRDIR)/theories/*.vo
# SSR_DEST=coq-fs/Ssreflect

SSRDIR=~/external/coq/math-comp/mathcomp/
SSR_PLUG=$(SSRDIR)/ssreflect.cma
SSR=$(SSRDIR)/ssreflect/*.vo
SSR_DEST=coq-fs/mathcomp_ssreflect

coq-fs/ssr:
	mkdir -p $(SSR_DEST)

ssr: coq-fs/ssr $(SSR_PLUG) $(SSR)
	$(shell cp -a $(SSR_PLUG) $(SSR_DEST)/ssreflect.cma)
	$(shell for i in $(SSR); do cp -a $$i $(SSR_DEST)/`basename $$i`; done)

SSR_ALG=$(SSRDIR)/algebra/*.vo
SSR_ALG_DEST=coq-fs/mathcomp_algebra

coq-fs/ssr-alg:
	mkdir -p $(SSR_ALG_DEST)

ssr-alg: coq-fs/ssr-alg $(SSR_ALG)
	$(shell for i in $(SSR_ALG); do cp -a $$i $(SSR_ALG_DEST)/`basename $$i`; done)

SSR_FIN=$(SSRDIR)/fingroup/*.vo
SSR_FIN_DEST=coq-fs/mathcomp_fingroup

coq-fs/ssr-fin:
	mkdir -p $(SSR_FIN_DEST)

ssr-fin: coq-fs/ssr-fin $(SSR_FIN)
	$(shell for i in $(SSR_FIN); do cp -a $$i $(SSR_FIN_DEST)/`basename $$i`; done)

SSR_SOL=$(SSRDIR)/solvable/*.vo
SSR_SOL_DEST=coq-fs/mathcomp_solvable

coq-fs/ssr-sol:
	mkdir -p $(SSR_SOL_DEST)

ssr-sol: coq-fs/ssr-sol $(SSR_SOL)
	$(shell for i in $(SSR_SOL); do cp -a $$i $(SSR_SOL_DEST)/`basename $$i`; done)

SSR_FLD=$(SSRDIR)/field/*.vo
SSR_FLD_DEST=coq-fs/mathcomp_field

coq-fs/ssr-fld:
	mkdir -p $(SSR_FLD_DEST)

ssr-fld: coq-fs/ssr-fld $(SSR_FLD)
	$(shell for i in $(SSR_FLD); do cp -a $$i $(SSR_FLD_DEST)/`basename $$i`; done)

lib-addons: ssr ssr-alg ssr-fin ssr-sol #ssr-fld

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

dist: all bcache
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

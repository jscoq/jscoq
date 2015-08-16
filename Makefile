.PHONY: clean upload all libs coq-tools jsoo-util jscoq32 jscoq64

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
SSRDIR=~/external/coq/ssr-git/
SSR_PLUG=$(SSRDIR)/src/ssreflect.cma
SSR=$(SSRDIR)/theories/*.vo
SSR_DEST=coq-fs/Ssreflect

coq-fs/ssr:
	mkdir -p coq-fs/Ssreflect

ssr: coq-fs/ssr $(SSR_PLUG) $(SSR)
	$(shell cp -a $(SSR_PLUG) $(SSR_DEST)/ssreflect.cma)
	$(shell for i in $(SSR); do cp -a $$i $(SSR_DEST)/`basename $$i`; done)

lib-addons: ssr

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

clean:
	$(MAKE) -C coq-js       clean
	$(MAKE) -C coq-tools    clean
	$(MAKE) -C coq-toplevel clean
# $(MAKE) -C jsoo-util clean
	rm -f *.cmi *.cmo *.ml.d *.mli.d Makefile.libs index.html
	rm -rf coq-fs

########################################################################
# Local stuff
upload: all
	ln -sf ide.html index.html
	rsync --delete -avzp index.html ide.html js css images coq-fs coq_pkg.json external ~/x80/rhino-coq/
	mkdir -p ~/x80/rhino-coq/coq-js/
	rsync -avzp coq-js/jscoq.js ~/x80/rhino-coq/coq-js/
# $(shell ./x80-sync.sh)

pau:
	rsync -avpz ~/research/jscoq pau:~/
	rsync -avpz pau:~/jscoq/ ~/research/pau-jscoq/

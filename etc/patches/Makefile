COQDIR = ${firstword ${wildcard ../../_vendor*/coq}}

ifeq ($(COQDIR),)
_ := ${error cannot find Coq sources dir}
endif

D = ../../etc/patches

%.patch: FORCE
	( cd $(COQDIR) && git diff ${shell ./_getfns.cjs $@} ) > $@

FORCE:
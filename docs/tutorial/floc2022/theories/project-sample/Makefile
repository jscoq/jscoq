
COQC = coqc
COQC_FLAGS = -R . simple

compile: One.vo Two.vo Three.vo

%.vo: %.v
	$(COQC) $(COQC_FLAGS) $*.v

One.vo: Two.vo
Three.vo: One.vo Two.vo

clean:
	rm -f *.vo *.vos *.vok *.glob .*.aux


MARKDOWN = python -m markdown -x extra
JSCOQ_URL = node_modules/jscoq

default: welcome.html
all-html: welcome.html more.html more-pkgs.html
all: all-html floc.coq-pkg

%.html: %.md res/header.in.html res/footer.in.html
	( cat res/header.in.html && $(MARKDOWN) $*.md && \
	  cat res/footer.in.html ) > $@

%.html: %.v
	JSCOQ_URL=$(JSCOQ_URL) npx jscoqdoc -s --no-index $*.v
	@rm -f coqdoc.css  # sorry

watch:
	npx lsynci -x '*.html' -x '*.css' -c 'make all-html'


COQC = npx jscoq sdk coqc

%.vo: %.v
	$(COQC) -R theories FLoC $<

floc.coq-pkg: theories/CooLib.vo
	npx jscoq --package floc --rootdir theories --top FLoC

clean:
	rm -f welcome.html more.html more-pkgs.html floc.json floc.coq-pkg
	rm -f $(addprefix theories/, *.vo *.vok *.vos *.glob .*.aux)
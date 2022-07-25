
MARKDOWN = python -m markdown -x extra
JSCOQ_URL = node_modules/jscoq

default: welcome.html
all: welcome.html more.html

%.html: %.md res/header.in.html res/footer.in.html
	( cat res/header.in.html && $(MARKDOWN) $*.md && \
	  cat res/footer.in.html ) > $@

%.html: %.v
	JSCOQ_URL=$(JSCOQ_URL) npx jscoqdoc -s --no-index $*.v
	@rm -f coqdoc.css  # sorry

watch:
	npx lsynci -x '*.html' -x '*.css' -c 'make all'
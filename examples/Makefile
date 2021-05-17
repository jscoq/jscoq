.PHONY: all

all: nahas_tutorial.html

nahas_tutorial.html: nahas_tutorial.v
	mkdir -p _build && cp $< _build/
	coqc _build/$<
	JSCOQ_URL=.. ../ui-js/jscoqdoc.js --no-index --no-lib-name --parse-comments _build/$<
	@rm coqdoc.css  # urghh

.PHONY: all
.PRECIOUS: _build/%.v

all: nahas_tutorial.html

WORD_SIZE ?= 32
-include ../config.inc

CONTEXT = jscoq+$(WORD_SIZE)bit
COQC = ../_build/install/$(CONTEXT)/bin/coqc
JSCOQ_CLI = ../_build/jscoq+64bit/dist/cli.js

all: examples.coq-pkg sqrt_2.html nahas_tutorial.html

examples.coq-pkg: ${addprefix _build/, nahas_tutorial.vo sqrt_2.vo} $(JSCOQ_CLI)
	$(JSCOQ_CLI) build --package examples --rootdir _build --no-recurse \
		--top Examples

_build/%.v: %.v
	mkdir -p _build && cp $< _build/

_build/%.vo: _build/%.v
	$(COQC) -R _build Examples $<

sqrt_2.html: _build/sqrt_2.v _build/sqrt_2.vo
	JSCOQ_URL=.. ../ui-js/jscoqdoc.js --no-index --no-lib-name --parse-comments $<
	@rm coqdoc.css  # urghh

nahas_tutorial.html: _build/nahas_tutorial.v _build/nahas_tutorial.vo
	JSCOQ_URL=.. ../ui-js/jscoqdoc.js --no-index --no-lib-name --parse-comments $<
	@rm coqdoc.css  # urghh
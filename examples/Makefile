.PHONY: all clean
.PRECIOUS: _build/%.v

### dev config
WORD_SIZE ?= 32
-include ../config.inc

CONTEXT = jscoq+$(WORD_SIZE)bit
COQC = ../_build/install/$(CONTEXT)/bin/coqc
JSCOQ_CLI = ../_build/$(CONTEXT)/dist-cli/cli.cjs
###

all: examples.coq-pkg examples.symb.json sqrt_2.html nahas_tutorial.html

examples.coq-pkg: ${addprefix _build/, nahas_tutorial.vo sqrt_2.vo} $(JSCOQ_CLI)
	$(JSCOQ_CLI) build --package examples --rootdir _build --no-recurse \
		--top Examples

examples.symb.json: examples.coq-pkg
	$(JSCOQ_CLI) run --require-pkg $< --inspect $@

_build/%.v: %.v
	mkdir -p _build && cp $< _build/

_build/%.vo: _build/%.v
	$(COQC) -R _build Examples $<

sqrt_2!JSCOQDOC_FLAGS = --template sqrt_2.template.html

%.html: _build/%.v _build/%.vo
	JSCOQ_URL=.. ../frontend/classic/js/jscoqdoc.cjs $($*!JSCOQDOC_FLAGS) \
	  --no-index --no-lib-name --parse-comments $<
	@rm coqdoc.css  # urghh

clean:
	rm -rf _build \
	  examples.coq-pkg examples.json sqrt_2.html nahas_tutorial.html

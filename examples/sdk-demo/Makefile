
REPO = https://github.com/coq-contribs/group-theory.git
WORKDIR = workdir

JSCOQ_CLI = npx jscoq

build: $(WORKDIR)
	cp dune-files/dune $(WORKDIR)/
	# Use current workspace, not jsCoq's
	$(JSCOQ_CLI) sdk dune build --root .

$(WORKDIR):
	git clone --recursive --depth=1 $(REPO) $@

setup:
	npm i
	docker pull jscoq/jscoq:sdk
	docker tag jscoq/jscoq:sdk jscoq:sdk
	rm -rf /tmp/jscoq-sdk  # cleanup in case there was a previous build there

clean:
	dune clean --root .

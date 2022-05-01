
REPO = https://github.com/coq-contribs/group-theory.git
WORKDIR = workdir

PATH := $(PWD)/bin:$(PATH)
export PATH

build: $(WORKDIR)
	cp dune-files/dune $(WORKDIR)/
	# Use current workspace, not jsCoq's
	dune build --root .

$(WORKDIR):
	git clone --recursive --depth=1 $(REPO) $@

clean:
	dune clean --root .

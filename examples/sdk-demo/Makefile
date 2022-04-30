
REPO = https://github.com/coq-community/coqoban
WORKDIR = workdir

PATH := $(PWD)/bin:$(PATH)
export PATH

build: $(WORKDIR)
	# Use current workspace, not jsCoq's
	dune build --root .

$(WORKDIR):
	git clone --recursive --depth=1 $(REPO) $@

clean:
	dune clean --root .

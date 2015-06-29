#!/bin/bash

# Names of the opam distributions
OCAMLDIST64=4.02.0+local-git-emilio-local
OCAMLDIST32=4.02.0+local-git-32-emilio-local

# build 32 bits parts
opam switch $OCAMLDIST32
eval `opam config env`
make jscoq32

opam switch $OCAMLDIST64
eval `opam config env`
make jscoq64

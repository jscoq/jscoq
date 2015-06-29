#!/bin/bash

# Names of the opam distributions
# OCAMLDIST64=4.02.0
# OCAMLDIST32=4.02.0+32bit

OCAMLDIST64=4.02.1
OCAMLDIST32=4.02.1+32bit

# build 32 bits parts
opam switch $OCAMLDIST32
eval `opam config env`
make jscoq32

opam switch $OCAMLDIST64
eval `opam config env`
make jscoq64

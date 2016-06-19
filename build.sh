#!/bin/bash

. ./build-common.sh

# build 32 bits parts
opam switch $OCAML_VER+32bit
eval `opam config env`
make -j $NJOBS jscoq32

if [ $? -ne 0 ]; then
   exit $?
fi

opam switch $OCAML_VER
eval `opam config env`
make -j $NJOBS jscoq64

# coq-tools must be built in 32 bits for now
opam switch $OCAML_VER+32bit
eval `opam config env`
make coq-tools
make libs

./cma_comp.sh

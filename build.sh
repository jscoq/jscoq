#!/bin/bash

set -e

. ./build-common.sh

# build 32 bits parts
opam switch $OCAML_VER+32bit
eval `opam config env`

make -j $NJOBS bytecode

# In previous versions of jsoo we needed to use a 64 jsoo due to high
# memory demands. This is fixed in jsoo 2.8.1

# opam switch $OCAML_VER
# eval `opam config env`

make -j $NJOBS js

# coq-tools must be built in 32 bits too
# opam switch $OCAML_VER+32bit
# eval `opam config env`

make coq-tools

# Switch to the same jsoo for plugin building
# opam switch $OCAML_VER
# eval `opam config env`

make libs
make plugin-comp

npm install

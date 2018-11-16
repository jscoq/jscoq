#!/bin/bash

set -e

. ./build-common.sh

# build 32 bits parts
opam switch $OCAML_VER+32bit
eval `opam config env`

# Build jscoq + libraries
make jscoq

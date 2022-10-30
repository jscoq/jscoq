#!/bin/bash

NJOBS=4
VERB= # -vv

# Default OCaml version
OCAML_VER=4.12.0
WRITE_CONFIG=no

if [ -e config.inc ] ; then . config.inc
else WRITE_CONFIG=yes ; fi

install_ocaml() {
  opam switch create default ocaml-base-compiler.$OCAML_VER
  eval `opam env`
}

install_deps() {
  opam update
  opam pin add -y -n --kind=path jscoq .
  opam install -y --deps-only $VERB -j $NJOBS jscoq
  opam pin remove jscoq
}

if [ $WRITE_CONFIG == yes ] ; then echo "WORD_SIZE=64" > config.inc ; fi

install_ocaml
install_deps

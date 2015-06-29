#!/bin/bash

NJOBS=64
JS_OF_OCAML_DIR=~/external/js_of_ocaml

do_setup() {
  opam install -j $NJOBS ocamlfind camlp4 camlp5 base64 cppo ppx_tools higlo ocp-indent tyxml js_of_ocaml reactiveData
  pushd $JS_OF_OCAML_DIR
  make clean && make -j $NJOBS && make uninstall install
  popd
}

opam switch -j $NJOBS 4.02.1
eval `opam config env`
do_setup

opam switch -j $NJOBS 4.02.1+32bit
eval `opam config env`
do_setup


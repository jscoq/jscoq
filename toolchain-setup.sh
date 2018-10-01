#!/bin/bash

. ./build-common.sh

JS_OF_OCAML_DIR=~/external/js_of_ocaml

JSCOQ_DEPS="num ocamlfind camlp5 js_of_ocaml js_of_ocaml-ppx js_of_ocaml-lwt yojson ppx_deriving_yojson ppx_tools_versioned ppx_deriving"

VERB=
# VERB=-vv

do_setup() {

  jsoo_repo=https://github.com/ocsigen/js_of_ocaml.git

  # Pinning of js_of_ocaml
  # for pkg in js_of_ocaml{-ppx,-lwt,-compiler,}
  # do
  #   opam pin add -y ${VERB} ${pkg} ${jsoo_repo}
  # done

  opam install -y ${VERB} -j ${NJOBS} ${JSCOQ_DEPS}

}

#opam switch -j $NJOBS -y $OCAML_VER
#eval `opam config env`
#do_setup

opam switch -j $NJOBS -y create $OCAML_VER+32bit
eval `opam env`
do_setup


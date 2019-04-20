#!/bin/bash

OCAML_VER=4.07.1
NJOBS=4
VERB= # -vv

do_setup() {

  # jsoo_repo=https://github.com/ocsigen/js_of_ocaml.git

  # Pinning of js_of_ocaml
  # for pkg in js_of_ocaml{-ppx,-lwt,-compiler,}
  # do
  #   opam pin add -y ${VERB} ${pkg} ${jsoo_repo}
  # done

  opam pin add -y -n --kind=path jscoq .
  opam install -y --deps-only $VERB -j $NJOBS jscoq
  opam pin remove jscoq

}

if [ -e config.inc ] ; then . config.inc ; fi

if [ "$WORD_SIZE" != 64 ] ; then
  opam switch -j $NJOBS -y create $OCAML_VER+32bit
  eval `opam env`
fi

do_setup

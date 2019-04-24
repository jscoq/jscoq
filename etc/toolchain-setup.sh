#!/bin/bash

OCAML_VER=4.07.1
NJOBS=4
VERB= # -vv

WORD_SIZE=32

WRITE_CONFIG=no

for i in "$@"; do
    case $i in
        --32) WORD_SIZE=32; WRITE_CONFIG=yes ;;
        --64) WORD_SIZE=64; WRITE_CONFIG=yes ;;
        *) echo unknown option "'$i'". ; exit ;;
    esac
done

install_deps() {

  opam pin add -y -n --kind=path jscoq .
  opam install -y --deps-only $VERB -j $NJOBS jscoq
  opam pin remove jscoq

}

if [ -e config.inc ] ; then . config.inc
else WRITE_CONFIG=yes ; fi

if [ $WRITE_CONFIG == yes ] ; then echo "WORD_SIZE=$WORD_SIZE" > config.inc ; fi

case $WORD_SIZE in
    32) opam switch -j $NJOBS create jscoq+32bit ocaml-variants.$OCAML_VER+32bit ;;
    64) opam switch -j $NJOBS create jscoq+64bit ocaml-base-compiler.$OCAML_VER ;;
esac

eval `opam env`

install_deps

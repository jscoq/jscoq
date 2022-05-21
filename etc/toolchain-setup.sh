#!/bin/bash

NJOBS=4
VERB= # -vv

# Default OCaml version
case `uname`-`uname -m` in
  Darwin-arm64) OCAML_VER=4.12.0 ;;  # older versions don't work on arm64
  *)            OCAML_VER=4.12.0 ;;
esac

# Default word size
case `uname` in
  Darwin) WORD_SIZE=64 ;; # macOS can no longer produce 32-bit objects
  *)      WORD_SIZE=32 ;;
esac

WRITE_CONFIG=no

if [ -e config.inc ] ; then . config.inc
else WRITE_CONFIG=yes ; fi

for i in "$@"; do
  case $i in
    --32) WORD_SIZE=32; WRITE_CONFIG=yes ;;
    --64) WORD_SIZE=64; WRITE_CONFIG=yes ;;
    *)    echo "unknown option '$i'."; exit ;;
  esac
done

create_switch() {

  case $WORD_SIZE in
    32) switch_name=jscoq+32bit; packages="ocaml-variants.$OCAML_VER+options,ocaml-option-32bit";;
    64) switch_name=jscoq+64bit; packages=ocaml-base-compiler.$OCAML_VER ;;
  esac

  opam switch -j $NJOBS create $switch_name --packages=$packages
  opam switch $switch_name || exit
  eval `opam env`

}

install_deps() {

  opam update

  opam pin add -y -n --kind=path jscoq .
  opam install -y --deps-only $VERB -j $NJOBS jscoq
  opam pin remove jscoq

}

post_install() {

  # Brutally remove ocamlopt from the switch when building 32-bit
  # on macOS.
  # 32-bit native compilation on macOS is broken and we found no other
  # way to disable it.
  # This has to take place only after install_deps.
  case `uname`/$WORD_SIZE in
    Darwin/32) rm -f $OPAM_SWITCH_PREFIX/bin/ocamlopt* ;;
  esac

}

if [ $WRITE_CONFIG == yes ] ; then echo "WORD_SIZE=$WORD_SIZE" > config.inc ; fi

create_switch
install_deps
post_install

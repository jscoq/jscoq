#!/bin/bash

set -x

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

# Dune compilation breaks if use a CI variable lol
JSCOQ_LOCAL=no
JSCOQ_CI=no

# Process argument
for i in "$@"; do
  case $i in
    --32) WORD_SIZE=32 ;;
    --64) WORD_SIZE=64 ;;
    --ci) JSCOQ_CI=yes ;;
    --local) JSCOQ_LOCAL=yes ;;
    *)    echo "unknown option '$i'."; exit ;;
  esac
done

# Build switch name
if [ "$JSCOQ_LOCAL" = "yes" ] ; then
  switch_name=.
else
  switch_name=jscoq+"$WORD_SIZE"bit
fi

create_switch() {

  case $WORD_SIZE in
    32) packages="ocaml-variants.$OCAML_VER+options,ocaml-option-32bit" ;;
    64) packages=ocaml-base-compiler.$OCAML_VER ;;
  esac

  # In CI _opam is setup by setup-ocaml action
  if [ "$JSCOQ_CI" = "no" ] ;
  then
      opam switch -j $NJOBS create $switch_name --packages=$packages -y
  fi
  if [ "$JSCOQ_LOCAL" = "no" ] ;
  then
      opam switch $switch_name || exit
  fi
}

install_deps() {

  if [ "$JSCOQ_CI" = "no" ] ;
  then
      opam update
      opam pin add -y -n --kind=path jscoq .
  fi

  # Setup-ocaml action does perform the pinning
  opam install -y --deps-only $VERB -j $NJOBS jscoq

  if [ "$JSCOQ_CI" = "no" ] ;
  then
      opam pin remove jscoq
  fi
}

post_install() {

  # Brutally remove ocamlopt from the switch when building 32-bit
  # on macOS.
  # 32-bit native compilation on macOS is broken and we found no other
  # way to disable it.
  # This has to take place only after install_deps.
  eval $(opam env)

  case `uname`/$WORD_SIZE in
    Darwin/32) rm -f $OPAM_SWITCH_PREFIX/bin/ocamlopt* ;;
  esac

}

# Write config
echo -e "WORD_SIZE=$WORD_SIZE\nSWITCH_NAME=$switch_name" > config.inc ;

create_switch
install_deps
post_install

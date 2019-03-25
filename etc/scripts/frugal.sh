#!/bin/sh
#
# Frugal Coq installation
#
# A lightweight method to compile addon libraries with locally compiled Coq
# (from Dune build)
#

COQVER=v8.10
COQDIR=coq-external/coq-$COQVER

frugal_symlink() { echo "$2 -> $1"; rm -f $2; ln -sf $1 $2; }

for d in _build/*/$COQDIR; do
    mkdir -p $d/bin
    frugal_symlink   ../topbin/coqtop_bin.exe     $d/bin/coqtop
    frugal_symlink   ../topbin/coqc_bin.exe       $d/bin/coqc
    frugal_symlink   ../tools/coqdep.exe          $d/bin/coqdep
    frugal_symlink   ../tools/coq_makefile.exe    $d/bin/coq_makefile
done

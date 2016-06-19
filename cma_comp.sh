#!/bin/sh

set -x

JSOO_CC="js_of_ocaml"
SED_CC="sed -i 's/(function(){return this}())//g'"

find coq-pkgs \( -name *.cma -or -name *.cmo \) -exec js_of_ocaml '{}' -o '{}'.js \;
find coq-pkgs \( -name *.cma -or -name *.cmo \) -exec sed -i "s/(function(){return this}())//g" '{}'.js \;


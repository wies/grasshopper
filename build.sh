#!/bin/bash

source bin/osx_gnu.sh

set -e

DIRS="-Is src/util,src/formulas,src/backends,src/programs,src/frontends/spl,src/prover,src/sl,src/verifier,src/locust,src/main"
TARGET="src/main/grasshopper src/main/vizmodel "
FLAGS="-cflag -g -lflag -g -libs unix,str $DIRS"
OCAMLBUILD=ocamlbuild

ocb()
{
    $OCAMLBUILD $FLAGS $*
}

if [ $# -eq 0 ]; then
    action=native
else
    action=$1;
    shift
fi

case $action in
    clean)  ocb -clean;;
    native) ocb ${TARGET//" "/".native "} ;;
    byte)   ocb ${TARGET//" "/".byte "} ;;
    all)    ocb ${TARGET//" "/".native "} ${TARGET//" "/".byte "} ;;
    prof)   ocb ${TARGET//" "/".p.native "} ;;
    tests)  bin/regression-tests $@ ;;
    depend) echo "Not needed.";;
    smt-lib) bin/generate-smtlib-benchmarks $@ ;;
    *)      echo "Unknown action $action";;
esac;


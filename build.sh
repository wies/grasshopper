#!/bin/sh

set -e

DIRS="-Is src,src/sl,src/interProcedural"
TARGET="src/interpolate src/sl/slprover "
FLAGS="-cflag -g -lflag -g -libs unix,str $DIRS"
OCAMLBUILD=ocamlbuild

ocb()
{
    $OCAMLBUILD $FLAGS $*
}

rule() {
    case $1 in
    clean)  ocb -clean;;
    native) ocb ${TARGET//" "/".native "} ;;
    byte)   ocb ${TARGET//" "/".byte "} ;;
    all)    ocb ${TARGET//" "/".native "} ${TARGET//" "/".byte "} ;;
    prof)   ocb $TARGET1.p.native ;;
    depend) echo "Not needed.";;
    *)      echo "Unknown action $1";;
    esac;
}

if [ $# -eq 0 ]; then
    rule native
else
    while [ $# -gt 0 ]; do
        rule $1;
        shift
    done
fi

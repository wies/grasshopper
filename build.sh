#!/bin/sh

set -e

TARGET1=src/main 
FLAGS="-cflag -g -lflag -g -libs unix,str"
OCAMLBUILD=ocamlbuild

ocb()
{
    $OCAMLBUILD $FLAGS $*
}

rule() {
    case $1 in
    clean)  ocb -clean;;
    native) ocb $TARGET1.native ;;
    byte)   ocb $TARGET1.byte ;;
    all)    ocb $TARGET1.native $TARGET1.byte ;;
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

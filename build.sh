#!/bin/bash

set -e

DIRS="-Is src/util,src/smtlib,src/programs,src/prover,src/grass,src/sl,src/analysis,src/main"
TARGET="src/main/grassprover src/main/slprover src/main/analyzer src/main/grasshopper "
FLAGS="-cflag -g -lflag -g -libs unix,str $DIRS"
OCAMLBUILD=ocamlbuild

ocb()
{
    $OCAMLBUILD $FLAGS $*
}

distro()
{
    test -s grasshopper && echo "Directory grasshopper already exists. Aboarding." && exit 0

    REPO=`svn info | grep URL | awk '{print $2}'`
    DATE=`date +%Y-%m-%d`

    svn export $REPO grasshopper

    RMDATE=`date +%B\ %d,\ %Y`

    cat README | sed s/\$DATE/"$RMDATE"/ > grasshopper/README

    tar -czvf grasshopper-$DATE.tar.gz grasshopper
    rm -rf grasshopper
}

rule() {
    case $1 in
    clean)  ocb -clean;;
    native) ocb ${TARGET//" "/".native "} ;;
    byte)   ocb ${TARGET//" "/".byte "} ;;
    all)    ocb ${TARGET//" "/".native "} ${TARGET//" "/".byte "} ;;
    prof)   ocb $TARGET1.p.native ;;
    depend) echo "Not needed.";;
    distro) distro ;;
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

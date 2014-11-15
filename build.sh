#!/bin/bash

source osx_gnu.sh

set -e

DIRS="-Is src/util,src/formulas,src/smtlib,src/programs,src/frontends/spl,src/prover,src/sl,src/analysis,src/main"
TARGET="src/main/grasshopper src/main/vizmodel "
FLAGS="-cflag -g -lflag -g -libs unix,str $DIRS"
OCAMLBUILD=ocamlbuild

ocb()
{
    $OCAMLBUILD $FLAGS $*
}

distro()
{
    test -s grasshopper && echo "Directory grasshopper already exists. Aborting." && exit 0

    REPO=`svn info | grep URL | awk '{print $2}'`
    svn export $REPO grasshopper

    RMDATE=`date +%B\ %d,\ %Y`
    cat README | sed s/\$DATE/"$RMDATE"/ > grasshopper/README

    tar -czvf grasshopper.tar.gz grasshopper
    rm -rf grasshopper
}

smtlib()
{
    ls *.smt2 2>/dev/null && echo "Remove existing SMT-LIB files to proceed. Aborting." && exit 0
    
    for sets in "" "-smtsets"; do 
      echo "Generating uninstantiated$sets benchmarks..."
      ./regression-tests $sets -noverify -noinst -dumpvcs -lint -smtpatterns > /dev/null
      rm soundness*.smt2
  
      echo "Post processing..."
      for file in *.smt2 
      do
          sed -i -e '/set-option/d' -e 's/unknown/unsat/'  $file
          LOGIC=`grep 'set-logic' $file | sed 's/(set-logic \([^)]*\))/\1/'`
          test -s $LOGIC || mkdir -p smt-lib/$LOGIC/grasshopper/uninstantiated
          mv $file smt-lib/$LOGIC/grasshopper/uninstantiated
      done
  
      echo "Generating instantiated$sets benchmarks..."
      ./regression-tests $sets -noverify -nostratify -dumpvcs -lint -smtpatterns > /dev/null
      rm soundness*.smt2
  
      echo "Post processing..."
      for file in *.smt2 
      do
          sed -i -e '/set-option/d' -e 's/unknown/unsat/'  $file
          LOGIC=`grep 'set-logic' $file | sed 's/(set-logic \([^)]*\))/\1/'`
          test -s $LOGIC || mkdir -p smt-lib/$LOGIC/grasshopper/instantiated
          mv $file smt-lib/$LOGIC/grasshopper/instantiated
      done
    done
}

rule() {
    case $1 in
    clean)  ocb -clean;;
    native) ocb ${TARGET//" "/".native "} ;;
    byte)   ocb ${TARGET//" "/".byte "} ;;
    all)    ocb ${TARGET//" "/".native "} ${TARGET//" "/".byte "} ;;
    prof)   ocb ${TARGET//" "/".p.native "} ;;
    depend) echo "Not needed.";;
    distro) distro ;;
    smt-lib) smtlib ;;
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

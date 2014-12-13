#!/bin/bash

source bin/osx_gnu.sh

set -e

DIRS="-Is src/util,src/formulas,src/backends,src/programs,src/frontends/spl,src/prover,src/sl,src/verifier,src/main"
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

generate()
{
    # COMMIT_ID and COMMON_ARGS should be defined

    VAR_ARGS="$@"
    OUTDIR=smtlib/${COMMIT_ID}$(echo $VAR_ARGS | tr -d " ")

    [ -d $OUTDIR ] && {
      echo "Looks like benchmarks already generated, skipping (delete $OUTDIR to force generation)"
      return
    }

    echo "Generating benchmarks with arguments ${VAR_ARGS}..."
    ./bin/regression-tests $COMMON_ARGS $VAR_ARGS > /dev/null
    rm soundness*.smt2

    mkdir -p $OUTDIR
    echo "Post processing..."
    for file in *.smt2
    do
        sed -i -e '/set-option/d' -e 's/unknown/unsat/'  $file
        LOGIC=`grep 'set-logic' $file | sed 's/(set-logic \([^)]*\))/\1/'`
        # test -s $LOGIC || mkdir -p smt-lib/$LOGIC/grasshopper/uninstantiated
        mv $file $OUTDIR
    done
}

smtlib()
{
    ls *.smt2 2>/dev/null && echo "Remove existing SMT-LIB files to proceed. Aborting." && exit 0

    COMMIT_ID="$(git log -1 --format="%cd-%h" --date=short)"
    COMMON_ARGS="-lint -noverify -dumpvcs -smtpatterns"

    generate "-nostratify"
    generate "-nostratify -smtsets"
    generate "-noinst"
    generate "-noinst -smtsets"
    generate "-noinst -nomodifiesopt"
    generate "-noinst -smtsets -nomodifiesopt"

    ## for kshitij's testing infrastructure
    [ -d "../test/benchmarks" ] && (
      rsync -r smtlib/ ../test/benchmarks/grasshopper/
      cd ../test/benchmarks
      LISTFILE=grasshopper_${COMMIT_ID}.list
      find grasshopper/$COMMIT_ID* -iname "*.smt2" >$LISTFILE
      wc -l $LISTFILE
    )
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
    distro) distro ;;
    smt-lib) smtlib ;;
    *)      echo "Unknown action $action";;
esac;


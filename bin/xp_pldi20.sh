#!/bin/bash

source bin/osx_gnu.sh

#echo "Building Grasshopper"
#./build.sh

FILES1="flows ccm multiset-ccm multipair-ccm give-up link"
FILES2="hashtbl-give-up"
FILES3="hashtbl-link"
FILES4="b+-tree"
FILES5="b-link-core"
FILES6="b-link-half"
FILES7="b-link-full"
FILES8="ordered_type array_util"

timesfile=/tmp/times-grasshopper
locfile=/tmp/loc-grasshopper

SPLPATH=tests/spl/flows

run()
{
    name="${1}"
    shift
    echo -n "$name"
    rm -f $timesfile $locfile
    for f in $@ ; do
        #echo "processessing $f"
        python bin/line-counter.py $SPLPATH/$f.spl >> $locfile
        { TIMEFORMAT=%3R; time ./grasshopper.native $SPLPATH/$f.spl -module $f ; } 2>> $timesfile
    done
    awk -F "\t" '{specs+=$1; progs+=$2; total+=$3} END{printf("\t& %d\t& %d\t& %d", progs, specs, total);}' $locfile
    awk '{sum+=$1;} END{printf("\t& %d\n", int(sum+0.5));}' $timesfile
}

echo -e "; Module\t& Code\t& Proof\t& Total\t& Time"
run "Flow library" $FILES1
run "Array library" $FILES8
run "Hash tbl (link)" $FILES2
run "Hash tbl (g-u)" $FILES3
run "B+ tree" $FILES4
run "B-link (core)" $FILES5
run "B-link (h s)" $FILES6
run "B-tree (f s)" $FILES7

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
timestotalfile=/tmp/times-total-grasshopper
loctotalfile=/tmp/loc-total-grasshopper

SPLPATH=tests/spl/flows

run()
{
    name="${1}"
    tabs=$((2 - ${#name} / 8))
    echo -n "$name"
    perl -E "print \"\t\" x $tabs"
    shift
    rm -f $timesfile $locfile
    for f in $@ ; do
        #echo "processessing $f"
        python bin/line-counter.py $SPLPATH/$f.spl >> $locfile
        { TIMEFORMAT=%3R; time ./grasshopper.native $SPLPATH/$f.spl -module $f ; } 2>> $timesfile
    done
    awk -F "\t" '{specs+=$1; progs+=$2; total+=$3} END{printf("\t& %d\t& %d\t& %d", progs, specs, total);}' $locfile
    awk -F "\t" '{specs+=$1; progs+=$2; total+=$3} END{printf("%d\t%d\t%d\n", progs, specs, total);}' $locfile >> $loctotalfile
    awk '{sum+=$1;} END{printf("\t& %d\n", int(sum+0.5));}' $timesfile
    awk '{sum+=$1;} END{printf("%d\n", int(sum+0.5));}' $timesfile >> $timestotalfile

}

rm -f $loctotalfile $timestotalfile
echo -e "; Module\t\t& Code\t& Proof\t& Total\t& Time"
run "Flow library" $FILES1
run "Array library" $FILES8
run "B-link (core)" $FILES5
run "B-link (half split)" $FILES6
run "B-tree (full split)" $FILES7
run "B+ tree" $FILES4
run "Hash table (link)" $FILES2
run "Hash table (give-up)" $FILES3

echo -n -e "Total\t\t"
awk -F "\t" '{progs+=$1; specs+=$2; total+=$3} END{printf("\t& %d\t& %d\t& %d", progs, specs, total);}' $loctotalfile
awk '{sum+=$1;} END{printf("\t& %d\n", int(sum+0.5));}' $timestotalfile

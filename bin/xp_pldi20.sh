#!/bin/bash

source bin/osx_gnu.sh

#echo "Building Grasshopper"
#./build.sh

FILES1="flows ccm multiset-ccm inset-flows lock-coupling"
FILES2="hashtbl-give-up"
FILES3="hashtbl-link-simple"
FILES4="b+-tree"
FILES5="b-link-core"
FILES6="b-link-half"
FILES7="b-link-full"
FILES8="ordered_type array_util"
FILES9="list-coupling"

timesfile=/tmp/times-grasshopper
locfile=/tmp/loc-grasshopper
timestotalfile=/tmp/times-total-grasshopper
loctotalfile=/tmp/loc-total-grasshopper
outputfile=/tmp/implementations-table

SPLPATH=tests/spl/flows

run()
{
    name="${1}"
    tabs=$((2 - ${#name} / 8))
    echo  "\\hline" >> $outputfile
    echo -n "$name" >> $outputfile
    perl -E "print \"\t\" x $tabs" >> $outputfile
    shift
    rm -f $timesfile $locfile
    for f in $@ ; do
        #echo "processessing $f"
        python bin/line-counter.py $SPLPATH/$f.spl >> $locfile
        echo "./grasshopper.native $SPLPATH/$f.spl -module $f"
        { TIMEFORMAT=%3R; time ./grasshopper.native $SPLPATH/$f.spl -module $f 2>&1 ; } 2>> $timesfile
        retcode=$?
        if [ $retcode -ne 0 ]; then
            echo -e "\nGrasshopper exited with errors on file $f.spl.\n"
        fi
    done
    awk -F "\t" '{specs+=$1; progs+=$2; total+=$3} END{printf("\t& %d\t& %d\t& %d", progs, specs, total);}' $locfile >> $outputfile
    awk -F "\t" '{specs+=$1; progs+=$2; total+=$3} END{printf("%d\t%d\t%d\n", progs, specs, total);}' $locfile >> $loctotalfile
    awk '{sum+=$1;} END{printf("\t& %d\\\\\n", int(sum+0.5));}' $timesfile >> $outputfile
    awk '{sum+=$1;} END{printf("%d\n", int(sum+0.5));}' $timesfile >> $timestotalfile
}

rm -f $loctotalfile $timestotalfile $outputfile

echo -e "; Module\t\t& Code\t& Proof\t& Total\t& Time" >> $outputfile
run "Flow library" $FILES1
run "Array library" $FILES8
run "B+ tree" $FILES4
run "B-link (core)" $FILES5
run "B-link (half split)" $FILES6
run "B-tree (full split)" $FILES7
run "Hash table (link)" $FILES2
run "Hash table (give-up)" $FILES3
run "Lock-coupling list" $FILES9

echo -n -e "Total\t\t" >> $outputfile
awk -F "\t" '{progs+=$1; specs+=$2; total+=$3} END{printf("\t& %d\t& %d\t& %d", progs, specs, total);}' $loctotalfile >> $outputfile
awk '{sum+=$1;} END{printf("\t& %d\n", int(sum+0.5));}' $timestotalfile >> $outputfile

echo ""
cat $outputfile

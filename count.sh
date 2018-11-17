#!/bin/bash

for f in tests/spl/include/ordered_type.spl tests/spl/reloc/*.spl 
do
    echo $f >> lines.txt
    python bin/line-counter.py $f >> lines.txt
    echo >> lines.txt
done

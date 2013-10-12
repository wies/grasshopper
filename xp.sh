#!/bin/bash

TESTS1="
sl_traverse tests/spl/sl_traverse.spl pass
sl_dispose tests/spl/sl_dispose.spl pass
sl_copy tests/spl/sl_copy.spl pass
sl_reverse tests/spl/sl_reverse.spl pass
sl_concat tests/spl/sl_concat.spl pass
sl_filter tests/spl/sl_filter.spl pass
sl_remove tests/spl/sl_remove.spl pass
sl_insert tests/spl/sl_insert.spl pass
"

TESTS2="
recursive_traverse tests/spl/rec_traverse.spl pass
recursive_dispose tests/spl/rec_dispose.spl pass
recursive_copy tests/spl/rec_copy.spl pass
recursive_reverse tests/spl/rec_reverse.spl pass
recursive_concat tests/spl/rec_concat.spl pass
recursive_filter tests/spl/rec_filter.spl pass
recursive_remove tests/spl/rec_remove.spl pass
recursive_insert tests/spl/rec_insert.spl pass
"

TESTS3="
dl_traverse tests/spl/dl_traverse.spl pass
dl_dispose tests/spl/dl_dispose.spl pass
dl_copy tests/spl/dl_copy.spl pass
dl_reverse tests/spl/dl_reverse.spl pass
dl_concat tests/spl/dl_concat.spl pass
dl_filter tests/spl/dl_filter.spl pass
dl_remove tests/spl/dl_remove.spl pass
dl_insert tests/spl/dl_insert.spl pass
"

TESTS4="
sls_traverse tests/spl/sls_traverse.spl pass
sls_dispose tests/spl/sls_dispose.spl pass
sls_copy tests/spl/sls_copy.spl pass
sls_reverse tests/spl/sls_reverse.spl pass
sls_concat tests/spl/sls_concat.spl pass
sls_filter tests/spl/sls_filter.spl pass
sls_remove tests/spl/sls_remove.spl pass
sls_insert tests/spl/sls_insert.spl pass
"

TESTS5="
sls_insertion_sort tests/spl/sls_insertion_sort.spl pass
sls_merge_sort tests/spl/sls_merge_sort.spl pass
sls_quicksort tests/spl/sls_quicksort.spl pass
sls_strand_sort tests/spl/sls_strand_sort.spl pass
"

TESTS6="
union_find tests/spl/union_find.spl pass
"

echo "SLL loop"
OPTIONS=$@ time -f "Accumulated time: %Us." ./run-tests $TESTS1

echo "SLL rec"
OPTIONS=$@ time -f "Accumulated time: %Us." ./run-tests $TESTS2

echo "DLL"
OPTIONS=$@ time -f "Accumulated time: %Us." ./run-tests $TESTS3

echo "sorted SLL"
OPTIONS=$@ time -f "Accumulated time: %Us." ./run-tests $TESTS4

echo "sorting algo"
OPTIONS=$@ time -f "Accumulated time: %Us." ./run-tests $TESTS5

echo "union-find"
OPTIONS=$@ time -f "Accumulated time: %Us." ./run-tests $TESTS6


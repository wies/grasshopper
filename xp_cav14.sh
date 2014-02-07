#!/bin/bash

TESTS1="
sl_traverse             tests/spl/sl/sl_traverse.spl                        pass
sl_dispose              tests/spl/sl/sl_dispose.spl                         pass
sl_copy                 tests/spl/sl/sl_copy.spl                            pass
sl_reverse              tests/spl/sl/sl_reverse.spl                         pass
sl_concat               tests/spl/sl/sl_concat.spl                          pass
sl_filter               tests/spl/sl/sl_filter.spl                          pass
sl_remove               tests/spl/sl/sl_remove.spl                          pass
sl_insert               tests/spl/sl/sl_insert.spl                          pass
"

TESTS2="
recursive_traverse      tests/spl/sl/rec_traverse.spl                       pass
recursive_dispose       tests/spl/sl/rec_dispose.spl                        pass
recursive_copy          tests/spl/sl/rec_copy.spl                           pass
recursive_reverse       tests/spl/sl/rec_reverse.spl                        pass
recursive_concat        tests/spl/sl/rec_concat.spl                         pass
recursive_filter        tests/spl/sl/rec_filter.spl                         pass
recursive_remove        tests/spl/sl/rec_remove.spl                         pass
recursive_insert        tests/spl/sl/rec_insert.spl                         pass
"

TESTS3="
dl_traverse             tests/spl/dl/dl_traverse.spl                        pass
dl_dispose              tests/spl/dl/dl_dispose.spl                         pass
dl_copy                 tests/spl/dl/dl_copy.spl                            pass
dl_reverse              tests/spl/dl/dl_reverse.spl                         pass
dl_concat               tests/spl/dl/dl_concat.spl                          pass
dl_filter               tests/spl/dl/dl_filter.spl                          pass
dl_remove               tests/spl/dl/dl_remove.spl                          pass
dl_insert               tests/spl/dl/dl_insert.spl                          pass
"

TESTS4="
sls_traverse            tests/spl/sls/sls_traverse.spl                      pass
sls_dispose             tests/spl/sls/sls_dispose.spl                       pass
sls_copy                tests/spl/sls/sls_copy.spl                          pass
sls_reverse             tests/spl/sls/sls_reverse.spl                       pass
sls_concat              tests/spl/sls/sls_concat.spl                        pass
sls_filter              tests/spl/sls/sls_filter.spl                        pass
sls_remove              tests/spl/sls/sls_remove.spl                        pass
sls_insert              tests/spl/sls/sls_insert.spl                        pass
"

TESTS5="
sls_insertion_sort      tests/spl/sls/sls_insertion_sort.spl                pass
sls_merge_sort          tests/spl/sls/sls_merge_sort.spl                    pass
sls_quicksort           tests/spl/sls/sls_quicksort.spl                     pass
sls_strand_sort         tests/spl/sls/sls_strand_sort.spl                   pass
"

TESTS6="
union_find              tests/spl/union_find.spl                            pass
"

TESTS7="
sorted_set_contains     tests/spl/sl_sorted_set/contains.spl   contains     pass
sorted_set_delete       tests/spl/sl_sorted_set/delete.spl     delete       pass
sorted_set_difference   tests/spl/sl_sorted_set/difference.spl difference   pass
sorted_set_insert       tests/spl/sl_sorted_set/insert.spl     insert       pass
sorted_set_traverse     tests/spl/sl_sorted_set/traverse.spl   traverse     pass
sorted_set_union        tests/spl/sl_sorted_set/union.spl      union        pass
"

TESTS8="
bst_contains            tests/spl/tree/binary_search_tree.spl  contains         pass
bst_destroy             tests/spl/tree/binary_search_tree.spl  destroy          pass
bst_extract_max         tests/spl/tree/binary_search_tree.spl  extract_max      pass
bst_insert              tests/spl/tree/binary_search_tree.spl  insert           pass
bst_travers             tests/spl/tree/binary_search_tree.spl  traverse         pass
bst_remove              tests/spl/tree/binary_search_tree.spl  remove           pass
"

TESTS9="
skew_heap_insert        tests/spl/tree/skew_heap_no_content.spl  insert          pass
skew_heap_union         tests/spl/tree/skew_heap_no_content.spl  union           pass
skew_heap_extractMax    tests/spl/tree/skew_heap_no_content.spl  extractMax      pass
"

#echo "SLL loop"
#OPTIONS=$@ time -f "Accumulated time: %Us." ./run-tests $TESTS1

#echo "SLL rec"
#OPTIONS=$@ time -f "Accumulated time: %Us." ./run-tests $TESTS2

#echo "DLL"
#OPTIONS=$@ time -f "Accumulated time: %Us." ./run-tests $TESTS3

#echo "sorted SLL"
#OPTIONS=$@ time -f "Accumulated time: %Us." ./run-tests $TESTS4

#echo "sorting algo"
#OPTIONS=$@ time -f "Accumulated time: %Us." ./run-tests $TESTS5

#echo "union-find"
#OPTIONS=$@ time -f "Accumulated time: %Us." ./run-tests $TESTS6

echo "building Grasshopper"
./build.sh

echo "set implemented as sorted list (functional correctness)"
OPTIONS=$@ time -f "Accumulated time: %Us." ./run-tests-methods $TESTS7

echo "set implemented as binary search tree (functional correctness)"
OPTIONS=$@ time -f "Accumulated time: %Us." ./run-tests-methods $TESTS8

echo "skew heap (memory safety, tree-shape)"
OPTIONS=$@ time -f "Accumulated time: %Us." ./run-tests-methods $TESTS9

#!/bin/bash

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
bst_rotate_left         tests/spl/tree/binary_search_tree.spl  rotate_left      pass
bst_rotate_right        tests/spl/tree/binary_search_tree.spl  rotate_right     pass
"

TESTS9="
skew_heap_insert        tests/spl/tree/skew_heap_no_content.spl  insert          pass
skew_heap_union         tests/spl/tree/skew_heap_no_content.spl  union           pass
skew_heap_extractMax    tests/spl/tree/skew_heap_no_content.spl  extractMax      pass
"

echo "building Grasshopper"
./build.sh

echo "set implemented as sorted list (functional correctness)"
OPTIONS=$@ time -f "Accumulated time: %Us." ./run-tests-methods $TESTS7

echo "set implemented as binary search tree (functional correctness)"
OPTIONS=$@ time -f "Accumulated time: %Us." ./run-tests-methods $TESTS8

echo "skew heap (memory safety, tree-shape)"
OPTIONS=$@ time -f "Accumulated time: %Us." ./run-tests-methods $TESTS9

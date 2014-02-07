#!/bin/bash

TESTS1="
union-find_list_find    tests/spl/union_find.spl               find         pass
union-find_list_union   tests/spl/union_find.spl               union        pass
union-find_list_create  tests/spl/union_find.spl               create       pass
union-find_tree_find    tests/spl/tree/union_find_parent.spl   find         pass
union-find_tree_union   tests/spl/tree/union_find_parent.spl   union        pass
union-find_tree_create  tests/spl/tree/union_find_parent.spl   create       pass
"

TESTS2="
sorted-set_contains     tests/spl/sl_sorted_set/contains.spl   contains     pass
sorted-set_delete       tests/spl/sl_sorted_set/delete.spl     delete       pass
sorted-set_difference   tests/spl/sl_sorted_set/difference.spl difference   pass
sorted-set_insert       tests/spl/sl_sorted_set/insert.spl     insert       pass
sorted-set_traverse     tests/spl/sl_sorted_set/traverse.spl   traverse     pass
sorted-set_union        tests/spl/sl_sorted_set/union.spl      union        pass
"

TESTS3="
bst_contains            tests/spl/tree/binary_search_tree.spl  contains         pass
bst_destroy             tests/spl/tree/binary_search_tree.spl  destroy          pass
bst_extract_max         tests/spl/tree/binary_search_tree.spl  extract_max      pass
bst_insert              tests/spl/tree/binary_search_tree.spl  insert           pass
bst_travers             tests/spl/tree/binary_search_tree.spl  traverse         pass
bst_remove              tests/spl/tree/binary_search_tree.spl  remove           pass
bst_rotate_left         tests/spl/tree/binary_search_tree.spl  rotate_left      pass
bst_rotate_right        tests/spl/tree/binary_search_tree.spl  rotate_right     pass
"

TESTS4="
skew-heap_insert        tests/spl/tree/skew_heap_no_content.spl  insert          pass
skew-heap_union         tests/spl/tree/skew_heap_no_content.spl  union           pass
skew-heap_extractMax    tests/spl/tree/skew_heap_no_content.spl  extractMax      pass
"

echo "building Grasshopper"
./build.sh

echo "union-find: functional correctness (tree-view), path compaction (list-view)"
OPTIONS=$@ time -f "Accumulated time: %Us." ./run-tests-methods $TESTS1

echo "set implemented as sorted list (functional correctness)"
OPTIONS=$@ time -f "Accumulated time: %Us." ./run-tests-methods $TESTS2

echo "set implemented as binary search tree (functional correctness)"
OPTIONS=$@ time -f "Accumulated time: %Us." ./run-tests-methods $TESTS3

echo "skew heap (memory safety, tree-shape)"
OPTIONS=$@ time -f "Accumulated time: %Us." ./run-tests-methods $TESTS4

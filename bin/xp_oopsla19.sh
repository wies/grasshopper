#!/bin/bash

source bin/osx_gnu.sh

# Format: <test name> <spl file> <procedure> <expected result>
TESTS="
b+tree_inRange    ../implementations/b+-tree.spl             'inRange'  pass
b+tree_init       ../implementations/b+-tree.spl             'init'     pass
b+tree_findNext   ../implementations/b+-tree.spl             'findNext' pass
b+tree_member     ../implementations/b+-tree.spl             'member'   pass
b+tree_insert     ../implementations/b+-tree.spl             'insert'   pass
b+tree_delete     ../implementations/b+-tree.spl             'delete'   pass
b+tree_keyset     ../implementations/b+-tree.spl             'keyset_implies_leaf'     pass
b+-tree_inset_step   ../implementations/b+-tree.spl      'flowint_inset_step'     pass
b+-tree_proj   ../implementations/b+-tree.spl      'flowint_proj'     pass
b+-tree_cont   ../implementations/b+-tree.spl      'flowint_cont'     pass
b+-tree_step   ../implementations/b+-tree.spl      'flowint_step'     pass
b-link-tree_init ../implementations/b-link.spl           'init' pass
b-link-tree_findNext ../implementations/b-link.spl           'findNext' pass
b-link-tree_member   ../implementations/b-link.spl           'member'   pass
b-link-tree_insert   ../implementations/b-link.spl           'insert'   pass
b-link-tree_delete   ../implementations/b-link.spl           'delete'   pass
b-link-tree_keyset   ../implementations/b-link.spl           'keyset_implies_leaf'     pass
b-link-tree_lemma_fm   ../implementations/b-link.spl         'lemma_fm'     pass
b-link-tree_int_ind   ../implementations/b-link.spl      'lemma_int_ind_is_valid'     pass
b-link-tree_compute_int   ../implementations/b-link.spl      'compute_int'     pass
b-link-tree_cont_props   ../implementations/b-link.spl      'lemma_cont_props'     pass
b-link-tree_int_stable   ../implementations/b-link.spl      'lemma_int_stable'     pass
b-link-tree_inreach_impl_inset   ../implementations/b-link.spl      'inreach_impl_inset'     pass
b-link-tree_inset_step   ../implementations/b-link.spl      'flowint_inset_step'     pass
b-link-tree_inreach_step   ../implementations/b-link.spl      'flowint_inreach_step'     pass
b-link-tree_proj   ../implementations/b-link.spl      'flowint_proj'     pass
b-link-tree_cont   ../implementations/b-link.spl      'flowint_cont'     pass
b-link-tree_step   ../implementations/b-link.spl      'flowint_step'     pass
hashtbl_findNext  ../implementations/hashtbl.spl             'findNext' pass
hashtbl_member    ../implementations/hashtbl.spl             'member'   pass
hashtbl_insert    ../implementations/hashtbl.spl             'insert'   pass
hashtbl_delete    ../implementations/hashtbl.spl             'delete'   pass
hashtbl_keyset    ../implementations/hashtbl.spl             'keyset_implies_bucket'   pass
hashtbl_inreach_impl_inset   ../implementations/hashtbl.spl      'inreach_impl_inset'     pass
hashtbl_inset_step   ../implementations/hashtbl.spl      'flowint_inset_step'     pass
hashtbl_inreach_step   ../implementations/hashtbl.spl      'flowint_inreach_step'     pass
hashtbl_proj   ../implementations/hashtbl.spl      'flowint_proj'     pass
hashtbl_cont   ../implementations/hashtbl.spl      'flowint_cont'     pass
hashtbl_step   ../implementations/hashtbl.spl      'flowint_step'     pass
hashtbl-give-up_inRange  ../implementations/hashtbl-give-up.spl     'inRange'  pass
hashtbl-give-up_findNext ../implementations/hashtbl-give-up.spl     'findNext' pass
hashtbl-give-up_member   ../implementations/hashtbl-give-up.spl     'member'   pass
hashtbl-give-up_insert   ../implementations/hashtbl-give-up.spl     'insert'   pass
hashtbl-give-up_delete   ../implementations/hashtbl-give-up.spl     'delete'   pass
hashtbl-give-up_keyset   ../implementations/hashtbl-give-up.spl     'keyset_implies_bucket'   pass
hashtbl-give-up_inset_step   ../implementations/hashtbl-give-up.spl      'flowint_inset_step'     pass
hashtbl-give-up_proj   ../implementations/hashtbl-give-up.spl      'flowint_proj'     pass
hashtbl-give-up_cont   ../implementations/hashtbl-give-up.spl      'flowint_cont'     pass
hashtbl-give-up_step   ../implementations/hashtbl-give-up.spl      'flowint_step'     pass
"

echo "Building Grasshopper"
./build.sh

echo "Running benchmarks"
res=0
OPTIONS=$@ time -f "Elapsed user time: %Us.\nElapsed real time: %es." ./bin/run-tests $TESTS || res=$?
exit $res

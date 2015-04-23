#!/bin/bash

source bin/osx_gnu.sh

TESTS="
soudness2               tests/spl/soundness/soundness2.spl      fail
soudness3               tests/spl/soundness/soundness3.spl      fail
soudness4               tests/spl/soundness/soundness4.spl      fail
soudness5               tests/spl/soundness/soundness5.spl      fail
soudness6               tests/spl/soundness/soundness6.spl      fail
soudness7               tests/spl/soundness/soundness7.spl      fail
soudness8               tests/spl/soundness/soundness8.spl      fail
sl_traverse             tests/spl/sl/sl_traverse.spl            pass
sl_dispose              tests/spl/sl/sl_dispose.spl             pass
sl_copy                 tests/spl/sl/sl_copy.spl                pass
sl_reverse              tests/spl/sl/sl_reverse.spl             pass
sl_concat               tests/spl/sl/sl_concat.spl              pass
sl_filter               tests/spl/sl/sl_filter.spl              pass
sl_remove               tests/spl/sl/sl_remove.spl              pass
sl_insert               tests/spl/sl/sl_insert.spl              pass
recursive_traverse      tests/spl/sl/rec_traverse.spl           pass
recursive_dispose       tests/spl/sl/rec_dispose.spl            pass
recursive_copy          tests/spl/sl/rec_copy.spl               pass
recursive_reverse       tests/spl/sl/rec_reverse.spl            pass
recursive_concat        tests/spl/sl/rec_concat.spl             pass
recursive_filter        tests/spl/sl/rec_filter.spl             pass
recursive_remove        tests/spl/sl/rec_remove.spl             pass
recursive_insert        tests/spl/sl/rec_insert.spl             pass
dl_traverse             tests/spl/dl/dl_traverse.spl            pass
dl_dispose              tests/spl/dl/dl_dispose.spl             pass
dl_copy                 tests/spl/dl/dl_copy.spl                pass
dl_reverse              tests/spl/dl/dl_reverse.spl             pass
dl_concat               tests/spl/dl/dl_concat.spl              pass
dl_filter               tests/spl/dl/dl_filter.spl              pass
dl_remove               tests/spl/dl/dl_remove.spl              pass
dl_insert               tests/spl/dl/dl_insert.spl              pass
sls_traverse            tests/spl/sls/sls_traverse.spl          pass
sls_dispose             tests/spl/sls/sls_dispose.spl           pass
sls_copy                tests/spl/sls/sls_copy.spl              pass
sls_reverse             tests/spl/sls/sls_reverse.spl           pass
sls_concat              tests/spl/sls/sls_concat.spl            pass
sls_filter              tests/spl/sls/sls_filter.spl            pass
sls_remove              tests/spl/sls/sls_remove.spl            pass
sls_insert              tests/spl/sls/sls_insert.spl            pass
sls_insertion_sort      tests/spl/sls/sls_insertion_sort.spl    pass
sls_merge_sort          tests/spl/sls/sls_merge_sort.spl        pass
sls_quicksort           tests/spl/sls/sls_quicksort.spl         pass
sls_strand_sort         tests/spl/sls/sls_strand_sort.spl       pass
union_find              tests/spl/sl/union_find.spl             pass
list_set_contains       tests/spl/list_set/contains.spl         pass
list_set_delete         tests/spl/list_set/delete.spl           pass
list_set_difference     tests/spl/list_set/difference.spl       pass
list_set_insert         tests/spl/list_set/insert.spl           pass
list_set_traverse       tests/spl/list_set/traverse.spl         pass
list_set_union          tests/spl/list_set/union.spl            pass
bst_set                 tests/spl/tree/binary_search_tree.spl   pass
nested_list_destroy     tests/spl/nested_sl/destroy.spl         pass
nests_list_insert	tests/spl/nested_sl/insert.spl		pass
nests_list_remove	tests/spl/nested_sl/remove.spl		pass
nests_list_traverse	tests/spl/nested_sl/traverse.spl	pass
bst_set_trailrec        tests/spl/tree/binary_search_tree_tailrec.spl   pass
bst_set_so_trailrec     tests/spl/tree/binary_search_tree_shape_only_tailrec.spl   pass
skewheap		tests/spl/tree/skew_heap_no_content.spl pass
unionfind_tree          tests/spl/tree/union_find.spl           pass
"

generate()
{
    # COMMIT_ID and COMMON_ARGS should be defined

    VAR_ARGS="$@"
    OUTDIR=smtlib/${COMMIT_ID}$(echo $VAR_ARGS | tr -d " ")
    LOGFILE=out/${COMMIT_ID}$(echo $VAR_ARGS | tr -d " ").log

    [ -d $OUTDIR ] && {
      echo "Looks like benchmarks already generated, skipping (delete $OUTDIR to force generation)"
      return
    }

    echo "Generating benchmarks with arguments ${VAR_ARGS}..."
    OPTIONS="$COMMON_ARGS $VAR_ARGS" ./bin/run-tests $TESTS >$LOGFILE

    mkdir -p $OUTDIR
    echo "Post processing..."
    for file in *.smt2
    do
        LOGIC=`grep 'set-logic' $file | sed 's/(set-logic \([^)]*\))/\1/'`
        mv $file $OUTDIR
    done
}

smtlib-cav15()
{
    ls *.smt2 2>/dev/null && echo "Remove existing SMT-LIB files to proceed. Aborting." && exit 0

    ./build.sh

    COMMIT_ID="$(git log -1 --format="%cd-%h" --date=short)"

    COMMON_ARGS="-lint -noverify -dumpvcs"

    # Z3 UD
    generate "-smtsolver z3log -noinst"

    # Z3 UL
    generate "-smtsolver z3log -noinst -smtpatterns"

    # Z3 ULO
    generate "-smtsolver z3log -noinst -smtpatterns -optreach"

    # Z3 PM
    generate "-smtsolver z3log"

    # Z3 PL
    generate "-smtsolver z3log -smtpatterns"

    # Z3 PLO
    generate "-smtsolver z3log -smtpatterns -optreach"

    # CVC4 UD & UL
    generate "-smtsolver cvc4log -noinst -smtpatterns"

    # CVC4 ULO
    generate "-smtsolver cvc4log -noinst -smtpatterns -optreach -splitlemmas"

    # CVC4 PL
    generate "-smtsolver cvc4log -nostratify -smtpatterns"

    # CVC4 PLO
    generate "-smtsolver cvc4log -nostratify -smtpatterns -optreach -splitlemmas"

    # Prepare benchmarks for uploading to StarExec
    {
      cd smtlib &&
      mkdir ${COMMIT_ID} &&
      for i in ${COMMIT_ID}-smtsolverz3log/*.smt2; do
        file=$(basename $i)
        echo $file
        zip ${COMMIT_ID}/$file.zip ${COMMIT_ID}-*/$file
      done &&
      zip benchmarks-${COMMIT_ID}-forstarexec.zip ${COMMIT_ID}/*.zip
    }
}


mkdir -p out

# Calculating num of instantiations for naive algorithm
OPTIONS="-lint -noverify -nostratify" ./bin/run-tests $TESTS  |
  tr -d '\015' | sed 's/Checking.*\.\.\.//' | grep -vE "^(Passed |Failed |There were |\*\*\* )|ms\)$" |
  tee out/num_insts.txt

# Generate benchmarks
smtlib-cav15 | tee out/smtlib-cav15.log

_grasshopper() 
{
    local cur prev words cword split
    _init_completion -s || return

    opts="-basedir -v -q -stats -lint -model -nulledges -trace -dumpghp -dumpvcs -dumpcores -procedure -typeonly -noverify -robust -nomodifiesopt -optreach -noreach -noep -fullep -noinst -termgen -nostratify -nofixedpoint -abspreds -splitlemmas -smtsolver -smtpatterns -smtsets -smtarrays -bitvector -simplearrays -compile -help --help"

    case "${prev}" in
        -smtsolver)
            COMPREPLY=( $(compgen -W "z3 cvc4 cvc4mf z3+cvc4 z3+cvc4mf cvc4+cvc4mf z3+cvc4+cvc4mf" -- ${cur}) )
            return 0
            ;;
        -dumpghp)
            COMPREPLY=( $(compgen -W "0 1 2 3" -- ${cur}) )
            return 0
            ;;
        -termgen)
            COMPREPLY=( $(compgen -W "1 2 3 4 5 6 7 8 9" -- ${cur}) )
            return 0
            ;;
    esac
    case "${cur}" in
        -*)
            COMPREPLY=( $(compgen -W "${opts}" -- ${cur}) )
			return 0
			;;
        *)
            _filedir
			return 0
			;;
    esac

}
complete -F _grasshopper grasshopper.native

#   -procedure <string>  Only check the specified procedure
#   -termgen <num> Number of rounds to run the term generation procedure
#   -smtsolver <solver> Choose SMT solver (z3, cvc4, cvc4mf), e.g., 'z3+cvc4mf'
#   -compile <filename> Compile SPL program to a C program outputed as a file with the given name.


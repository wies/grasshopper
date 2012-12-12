#!/bin/sh

#that script should be run in the project root folder, i.e. ../../

z3_instantiate () {
    echo $1 
    time ./interpolate.native -sl2 -z3q tests/sl/$1
}

eager_instantiate () {
    echo $1 
    time ./interpolate.native -sl2 tests/sl/$1
}

z3_instantiate traverse_1
z3_instantiate traverse_2
z3_instantiate traverse_3

z3_instantiate insert_1
z3_instantiate insert_2
z3_instantiate insert_3
z3_instantiate insert_4

z3_instantiate remove_1
z3_instantiate remove_2
z3_instantiate remove_3

z3_instantiate concat_1
z3_instantiate concat_2
z3_instantiate concat_3

z3_instantiate reverse_1
z3_instantiate reverse_2
z3_instantiate reverse_3

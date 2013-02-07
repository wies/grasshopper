(* for the axioms generation *)
let with_reach_axioms = ref true
let with_alloc_axioms = ref true
let with_null_axioms = ref true
let encode_fields_as_arrays = ref false

(*tell whether we are instantiating the axioms or relying on z3.*)
let instantiate = ref true
    
(* if true, do more than local inst. *)
let use_aggressive_inst = ref false

let use_triggers = ref false

let sl_mode = ref true

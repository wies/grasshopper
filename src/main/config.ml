
(* for the axioms generation *)
let with_reach_axioms = ref true
let with_jp_axioms = ref true
let with_alloc_axioms = ref false
let with_null_axioms = ref false
let with_before_axiom = ref true


(*tell whether we are instantiating the axioms or relying on z3.*)
let instantiate = ref true
    
(* if true, do more than local inst. *)
let use_aggressive_inst = ref false

let use_triggers = ref false

let sl_mode = ref false

let default_opts_for_sl () =
  with_before_axiom := false;
  with_jp_axioms := false;
  with_alloc_axioms := true;
  with_null_axioms := true;
  sl_mode := true;
  use_aggressive_inst := false

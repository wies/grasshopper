(* for the axioms generation *)
let with_reach_axioms = ref true
let with_alloc_axioms = ref true
let with_null_axioms = ref true
let keep_sets = ref true
let encode_fields_as_arrays = ref false
let use_btwn = ref true

(* tell whether we are instantiating the axioms or relying on the prover. *)
let instantiate = ref true
(* where to save the model *)
let model_file = ref ""
(* just dump the queries don't solve. *)
let dump_only = ref false

(* print statistics *)
let print_stats = ref false

let smtsolver = ref "Z3"

let cmd_options =
  [("-v", Arg.Unit Debug.set_debug, "Display verbose messages");
   ("-stats", Arg.Set print_stats, "Print statistics");
   ("-noreach", Arg.Clear with_reach_axioms, "Omit axioms for reachability predicates");
   ("-noalloc", Arg.Clear with_alloc_axioms, "Omit axioms for alloc predicate");
   ("-nonull", Arg.Clear with_null_axioms, "Omit axioms for null");
   ("-m", Arg.Set_string model_file, "Produce model");
   ("-elimsets", Arg.Clear keep_sets, "Eliminate sets in FOL reduction");
   ("-usearrays", Arg.Set encode_fields_as_arrays, "Use arrays to encode fields");
   ("-usereachwo", Arg.Clear use_btwn, "Use ReachWo predicate instead of Btwn for reachability");
   ("-noinst", Arg.Clear instantiate, "Let the prover deal with the quantifiers");
   ("-dumponly", Arg.Set dump_only, "Just dump the VCs but don't solve them");
   ("-smtsolver", Arg.Set_string smtsolver, "Choose SMT solver (Z3, CVC4, MathSAT)")
  ]

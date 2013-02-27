(* for the axioms generation *)
let with_reach_axioms = ref true
let with_alloc_axioms = ref true
let with_null_axioms = ref true
let keep_sets = ref false
let encode_fields_as_arrays = ref false

(* tell whether we are instantiating the axioms or relying on the prover. *)
let instantiate = ref true
(* where to save the model *)
let model_file = ref ""
(* just dump the queries don't solve. *)
let dump_only = ref false


let cmd_options =
  [("-v", Arg.Unit Debug.set_debug, "Display verbose messages");
   ("-noreach", Arg.Clear with_reach_axioms, "Do not add axioms for reachability predicates");
   ("-noalloc", Arg.Clear with_alloc_axioms, "Omit axioms for alloc predicate");
   ("-nonull", Arg.Clear with_null_axioms, "Omit axioms for null");
   ("-m", Arg.Set_string model_file, "Produce model");
   ("-keepsets", Arg.Set keep_sets, "Keep sets in reduction");
   ("-noinst", Arg.Clear instantiate, "Let the prover deal with the quantifiers.");
   ("-dumponly", Arg.Set dump_only, "just dump the VCs, don't solve.")
  ]

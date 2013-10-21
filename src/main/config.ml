(* for the axioms generation *)
let with_reach_axioms = ref true
let keep_sets = ref true
let encode_fields_as_arrays = ref false
let with_ep = ref true
let backend_solver_has_set_theory = ref false

(* Flag that controls whether we are instantiating the axioms or relying on the prover. *)
let instantiate = ref true
let stratify = ref true
(* File name where counterexample model is saved. *)
let model_file = ref ""
(* Flag that controls whether the generated VCs are dumped to files. *)
let dump_smt_queries = ref false
(* Flag that controls whether the generated VCs are checked. *)
let verify = ref true
(* Flag that controls whether to stop after the 1st VCs that cannot be checked. *)
let robust = ref false

let dump_ghp = ref (-1)

(* Flag that controls whether statistics are printed. *)
let print_stats = ref false

(* The SMT solver that is used for checking VCs. *)
let smtsolver = ref "Z3"

(* optmisation: oldify fields only if modified *)
let optFieldMod = ref true
(* optmisation: self-framing clause for SL predicates *)
let optSelfFrame = ref true

(* Some experimental features, mostly for testing purpose *)
let experimental = ref false

let cmd_options =
  [("-v", Arg.Unit Debug.set_debug, " Display verbose messages");
   ("-dumpghp", Arg.Set_int dump_ghp, "<num>  Print intermediate program after specified simplification stage (num=0,1,2,3)");
   ("-noverify", Arg.Clear verify, " Do not check the generated verification conditions");
   ("-robust", Arg.Set robust, " Continue even if some verification condition cannot be checked");
   ("-stats", Arg.Set print_stats, " Print statistics");
   ("-model", Arg.Set_string model_file, "<file>  Produce counterexample model for the first failing verification condition");
   ("-noreach", Arg.Clear with_reach_axioms, " Omit axioms for reachability predicates");
   ("-noep", Arg.Clear with_ep, " Omit entry points");
   ("-elimsets", Arg.Clear keep_sets, " Eliminate sets in reduction to GRASS");
   ("-smtsets", Arg.Set backend_solver_has_set_theory, " Use set theory of SMT solver to encode sets");
   ("-smtarrays", Arg.Set encode_fields_as_arrays, " Use array theory of SMT solver to encode fields");
   ("-noinst", Arg.Clear instantiate, " Let the SMT solver deal with the quantifiers without prior instantiation");
   ("-nostratify", Arg.Clear stratify, " Instantiate quantifiers that satisfy stratified sort restrictions");
   ("-dumpvcs", Arg.Set dump_smt_queries, " Generate SMT-LIB 2 files for all verification conditions");
   ("-smtsolver", Arg.Set_string smtsolver, " Choose SMT solver (Z3, CVC4, MathSAT)");
   ("-noOptFieldMod", Arg.Clear optFieldMod, " Disable mod set analysis optimization for fields");
   ("-noOptSelfFrame", Arg.Clear optSelfFrame, " Disable generation of self-framing clauses for SL predicates");
   ("-x", Arg.Set experimental, " Enable some experimental feature")
  ]

(* Version string *)
let version = "0.3"

(* Base directory for includes *)
let base_dir = ref ""

(* Name of procedure that is to be checked *)
let procedure = ref None

(* File name where counterexample model is saved. *)
let model_file = ref ""

(* File name where counterexample trace is saved. *)
let trace_file = ref ""

(* Flags controlling the axioms generation *)
let with_reach_axioms = ref true
let encode_fields_as_arrays = ref false
let with_ep = ref true
let use_set_theory = ref false
let keep_types = ref false

(* Flag that controls whether we are instantiating the axioms or relying on the prover. *)
let instantiate = ref true
let stratify = ref true
(* Flag that controls whether unsat cores are dumped for each VC *)
let unsat_cores = ref false
(* Flag that controls whether the generated VCs are dumped to files. *)
let dump_smt_queries = ref false
(* Flag that controls whether the generated VCs use named assertions. *)
let named_assertions = true
(* Flag that controls whether the generated VCs are checked. *)
let verify = ref true
(* Flag that controls whether to stop after the first VC that cannot be proved. *)
let robust = ref false
(* Flag that enables error messages for on-the-fly checking *)
let flycheck_mode = ref false

(* Print internal representation of program at specified stage *)
let dump_ghp = ref (-1)

(* Flag that controls whether statistics are printed. *)
let print_stats = ref false

(* The SMT solver that is used for checking VCs. *)
let smtsolver = ref "Z3"

(* Always add trigger annotations for quantifiers in SMT queries *)
let smtpatterns = ref false

(* optmisation: oldify fields only if modified *)
let opt_field_mod = ref true
(* optmisation: self-framing clause for SL predicates *)
let optSelfFrame = ref false


let cmd_options =
  [("-basedir", Arg.Set_string base_dir, "<string>  Base directory for resolving include directives");
   ("-procedure", Arg.String (fun p -> procedure := Some p), "<string>  Only check the specified procedure");
   ("-model", Arg.Set_string model_file, "<file>  Produce counterexample model for the first failing verification condition");
   ("-trace", Arg.Set_string trace_file, "<file> Produce counterexample trace for the first failing verification condition");
   ("-lint", Arg.Set flycheck_mode, " Print error messages for on-the-fly checking");
   ("-dumpghp", Arg.Set_int dump_ghp, "<num>  Print intermediate program after specified simplification stage (num=0,1,2,3)");
   ("-dumpvcs", Arg.Set dump_smt_queries, " Generate SMT-LIB 2 files for all verification conditions");
   ("-core", Arg.Set unsat_cores, " Produce unsat cores with every unsat SMT query");
   ("-noverify", Arg.Clear verify, " Do not check the generated verification conditions");
   ("-robust", Arg.Set robust, " Continue even if some verification condition cannot be checked");
   ("-smtsolver", Arg.Set_string smtsolver, " Choose SMT solver (Z3, CVC4, CVC4MF)");
   ("-smtpatterns", Arg.Set smtpatterns, " Always add pattern annotations to quantifiers in SMT queries");
   ("-smtsets", Arg.Set use_set_theory, " Use solver's set theory to encode sets (if supported)");
   ("-smtarrays", Arg.Set encode_fields_as_arrays, " Use array theory of SMT solver to encode fields");
   ("-types", Arg.Set keep_types, " Keep type information in intermediate program");
   ("-noreach", Arg.Clear with_reach_axioms, " Omit axioms for reachability predicates");
   ("-noep", Arg.Clear with_ep, " Omit entry points");
   ("-noinst", Arg.Clear instantiate, " Let the SMT solver deal with the quantifiers without prior instantiation");
   ("-nostratify", Arg.Clear stratify, " Instantiate quantifiers that satisfy stratified sort restrictions");
   ("-noOptFieldMod", Arg.Clear opt_field_mod, " Disable mod set analysis optimization for fields");
   ("-optSelfFrame", Arg.Set optSelfFrame, " enable generation of self-framing clauses for SL predicates");
   ("-stats", Arg.Set print_stats, " Print statistics");
   ("-v", Arg.Unit Debug.more_verbose, " Display more messages");
   ("-q", Arg.Unit Debug.less_verbose, " Display less messages");
  ]

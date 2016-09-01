(* Version string *)
let version = "0.4 alpha"

(* Base directory for includes *)
let base_dir = ref ""

(* Name of procedure that is to be checked *)
let procedure = ref None

(* File name where counterexample model is saved. *)
let model_file = ref ""
(* Display the edges going to null in the model *)
let model_null_edge = ref false

(* File name where counterexample trace is saved. *)
let trace_file = ref ""

(* Flags controlling the axioms generation *)
let with_reach_axioms = ref true
let with_opt_reach_axioms = ref false
let encode_fields_as_arrays = ref false
let with_ep = ref true
let full_ep = ref false
let use_set_theory = ref false
let simple_arrays = ref false
    
(* Flag to switch between integer and bitvectors *)
let use_bitvector = ref false

(* Flag that controls whether we are instantiating the axioms or relying on the prover. *)
let instantiate = ref true
let stratify = ref true
(* Flag that controls whether predicates are treated as abstract *)
let abstract_preds = ref false
(* Flag that controls whether split lemmas are added *)
let split_lemmas = ref false
(* Flag that controls whether unsat cores are dumped for each VC *)
let unsat_cores = ref false
(* Flag that controls whether the generated VCs are dumped to files. *)
let dump_smt_queries = ref false
(* Flag that controls whether the generated VCs use named assertions. *)
let named_assertions = ref false
(* Flag that controls whether the generated VCs are checked. *)
let verify = ref true
(* Flat that controls whether the program is only type-checked. *)
let typeonly = ref false
(* Flat that controls whether the program is only simplified. *)
let simplify = ref false
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

(* The file that the SPL program converted into C is written to *)
let compile_to = ref ""

(* optmisation: oldify fields only if modified *)
let opt_field_mod = ref true

(* compute the congruence closure as a fixed point (horn clauses) *)
let ccFixedPoint = ref true

(* maximal number of term generation rounds *)
let term_gen_max_rounds = ref 2

let cmd_options =
  [("-basedir", Arg.Set_string base_dir, "<string>  Base directory for resolving include directives. Default: current working directory\n\nOptions for controlling error reporting and debug output:");
   ("-v", Arg.Unit Debug.more_verbose, " Display more messages");
   ("-q", Arg.Unit Debug.less_verbose, " Display fewer messages");
   ("-stats", Arg.Set print_stats, " Print statistics");
   ("-lint", Arg.Set flycheck_mode, " Print single line error messages for on-the-fly checking");
   ("-model", Arg.Set_string model_file, "<file>  Produce counterexample model for the first failing verification condition");
   ("-nulledges", Arg.Set model_null_edge, " Show the edges going to null in the model");
   ("-trace", Arg.Set_string trace_file, "<file>  Produce counterexample trace for the first failing verification condition");
   ("-dumpghp", Arg.Set_int dump_ghp, "<num>  Print intermediate program after specified simplification stage (num=0,1,2,3)");
   ("-dumpvcs", Arg.Set dump_smt_queries, " Generate SMT-LIB 2 files for all verification conditions");
   ("-dumpcores", Arg.Set unsat_cores, " Produce unsat cores with every unsat SMT query\n\nOptions for controlling what is checked:");
   ("-procedure", Arg.String (fun p -> procedure := Some p), "<string>  Only check the specified procedure");
   ("-typeonly", Arg.Set typeonly, " Only type-check the program");
   ("-simplify", Arg.Set simplify, " Only type-check the program and output a simplified version of the input program");
   ("-noverify", Arg.Clear verify, " Only type-check the program and generate verification conditions without checking");
   ("-robust", Arg.Set robust, " Continue even if some verification condition cannot be checked\n\nOptions for controlling verification condition generation:");
   ("-nomodifiesopt", Arg.Clear opt_field_mod, " Disable mod set analysis optimization for fields\n\nOptions for controlling the GRASS prover:");
   ("-optreach", Arg.Set with_opt_reach_axioms, " Use optimized but incomplete reachability axioms");
   ("-noreach", Arg.Clear with_reach_axioms, " Omit axioms for reachability predicates");
   ("-noep", Arg.Clear with_ep, " Omit axioms for entry points");
   ("-fullep", Arg.Set full_ep, " Generates more ep terms");
   ("-noinst", Arg.Clear instantiate, " Let the SMT solver deal with the quantifiers without prior instantiation");
   ("-termgen", Arg.Set_int term_gen_max_rounds, "<num> Number of rounds to run the term generation procedure");
   ("-nostratify", Arg.Clear stratify, " Instantiate quantifiers that satisfy stratified sort restrictions\n\nOptions for controlling backend solver:");
   ("-nofixedpoint", Arg.Clear ccFixedPoint, " Do not use fixed point for the congruence-closure");
   ("-abspreds", Arg.Set abstract_preds, " Treat predicates as abstract.");
   ("-splitlemmas", Arg.Set split_lemmas, " Add split lemmas for all terms of sort Loc");
   ("-smtsolver", Arg.Set_string smtsolver, "<solver> Choose SMT solver (z3, cvc4, cvc4mf), e.g., 'z3+cvc4mf'");
   ("-smtpatterns", Arg.Set smtpatterns, " Always add pattern annotations to quantifiers in SMT queries");
   ("-smtsets", Arg.Set use_set_theory, " Use solver's set theory to encode sets (if supported)");
   ("-smtarrays", Arg.Set encode_fields_as_arrays, " Use solver's array theory to encode fields");
   ("-bitvector", Arg.Set use_bitvector, " Use bitvector theory for integers\n\nOptions for compiler:");
   ("-simplearrays", Arg.Set simple_arrays, " Use simple array encoding");
   ("-compile", Arg.Set_string compile_to, "<filename> Compile SPL program to a C program outputed as a file with the given name.");
  ]

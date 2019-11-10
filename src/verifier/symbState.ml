(** {5 Symbolic execution based verifier V2} *)

open Util
open Grass
open GrassUtil
open Prog
open Printf

(** Symbolic values; grasshopper distinguishes between terms and forms,
  viper's silicon doesn't *)
type symb_val =
  | Term of term
  | Form of form

(** symbolic store maintains a mapping from grasshopper vars to symbolic vals
  ident -> symb_val . *)
(* Note: adding sort so we can remember type when we sub in symbolic vals *)
type symb_store = (ident * sort) IdMap.t
let empty_store = IdMap.empty

(** path condition (pc) stack
  A sequence of scopes a tuple of (identifier of pc, scope identifier V, set[V])
  set[V] is the set of path conditions.
  Note: scope identifiers are used to label branch and path conds obtained from two
  points of program execution.
 *)

(** path condition chunks are of shape (branch id, scope id, pc list)
 TODO: optimize symb_val list to use a set. *)
type pc_stack = (ident * ident * symb_val list) list

(** heap elements and symbolic heap
  The symbolic maintains a multiset of heap chunks which are
  of the form (obj, V, [Id -> V]) or predicate and list of args.
  *)
type heap_chunk =
  | Obj of (ident * sort) * symb_val IdMap.t
  | Pred of ident * symb_val list

type symb_heap = heap_chunk list

(** Symbolic State are records that are manipulated during execution:
  1. symbolic store; a mapping from variable names to symbolic values
  2. symbolic heap; records which locations, fields, access predicates are
     accessable along with symbolic values they carry.
  3. path condition stack; this carries all path conditions which are represnented
     as symbolic expressions.
 *)
type symb_state = {
    store: symb_store;
    pc: pc_stack;
    heap: symb_heap;
    old: symb_heap;
  }

let mk_fresh_symb_state =
  {store = empty_store; pc = []; heap = []; old = []}

(** Helpers to format prints *)
let lineSep = "\n--------------------\n"

let string_of_symb_val v =
    match v with
    | Term t -> string_of_term t
    | Form f -> string_of_form f

let string_of_pcset s =
  s
  |> List.map (fun ele -> (string_of_symb_val ele))
  |> String.concat ", "

let string_of_symb_val_list vals =
  vals
  |> List.map (fun v -> (string_of_symb_val v))
  |> String.concat ", "
  |> sprintf "[%s]"

let string_of_symb_store s =
  let string_of_ident_sort_pair p =
    match p with
    | (id, srt) -> (string_of_ident id) ^ ":" ^ (string_of_sort srt)
  in
  IdMap.bindings s
  |> List.map (fun (k, v) -> (string_of_ident k) ^ ":" ^ (string_of_ident_sort_pair v))
  |> String.concat ", "
  |> sprintf "{%s}"

let string_of_symb_val_map store =
  IdMap.bindings store
  |> List.map (fun (k, v) -> (string_of_ident k) ^ ":" ^ (string_of_symb_val v))
  |> String.concat ", "
  |> sprintf "{%s}"

let string_of_symb_fields fields =
  IdMap.bindings fields
  |> List.map (fun (k, v) -> (string_of_ident k) ^ ":" ^ (string_of_symb_val v))
  |> String.concat ", "
  |> sprintf "{%s}"

let string_of_pc_stack pc =
  pc
  |> List.map (fun (pc, scope_ident, vars) ->
      "(" ^ (string_of_ident pc) ^ ", " ^ (string_of_ident scope_ident) ^ ", "
      ^ (string_of_pcset vars) ^ ")")
  |> String.concat ", "
  |> sprintf "[%s]"

let string_of_hc chunk =
  match chunk with
  | Obj ((id, srt), symb_fields) ->
      sprintf "Obj(Id:%s, Sort:%s, Fields:%s)" (string_of_ident id) (string_of_sort srt) (string_of_symb_fields symb_fields)
  | Pred (id, symb_vals) -> sprintf "Pred(Id:%s, Args:%s)" (string_of_ident id) (string_of_symb_val_list symb_vals)

let string_of_heap h =
  h 
  |> List.map (fun ele -> (string_of_hc ele))
  |> String.concat ", "
  |> sprintf "[%s]"

let string_of_state s =
  let store = string_of_symb_store s.store in
  let pc = string_of_pc_stack s.pc in
  let heap = string_of_heap s.heap in
  let old = string_of_heap s.old in
  sprintf "Store: %s\nPCStack: %s\nHeap: %s\nOld: %s" store pc heap old

(** Entry point for the symbexec engine *)
let exec prog =
  (* TODO build up state by iterating over procs *)
  let exec_proc id proc =
    Debug.debug(fun() ->
      sprintf "%sProc Decl: %s\n"
      lineSep (string_of_ident id)
    );
    pr_proc Format.std_formatter proc 
  in
  IdMap.iter exec_proc prog.prog_procs

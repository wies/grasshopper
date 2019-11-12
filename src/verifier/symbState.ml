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

(** Symbolic store:
  maintains a mapping from grasshopper vars to symbolic vals
  ident -> symb_val . *)
(* Note: adding sort so we can remember type when we sub in symbolic vals *)
type symb_store = symb_val IdMap.t
let empty_store = IdMap.empty

(** havoc a list of terms into a symbolic store *)
let havoc_terms symb_store terms =
  List.fold_left
    (fun sm term ->
      match term with
      | App (_, _, _) -> failwith "tried to havoc a term that isn't a Var"
      | Var (id, srt) -> IdMap.add id (Term (mk_fresh_var srt "v")) sm)
    symb_store terms

(** path condition (pc) stack
  A sequence of scopes a tuple of (scope id, branch condition, [V])
  list[V] is the list of path conditions.
  Note: scope identifiers are used to label branche conditions 
    and path conds obtained from two points of program execution.
 *)

(** path condition chunks are of shape (scope id, branch cond, pc list)
 TODO: optimize symb_val list to use a set. *)
type pc_stack = (ident * symb_val * symb_val list) list

let pc_add_path_cond pc_stack pc_val =
  match pc_stack with
  | [] -> failwith "tried to add path cond to an empty stack"  
  | (sid, bc, pcs) :: stack' -> (sid, bc, pc_val :: pcs) :: stack'

let pc_push_new pc_stack scope_id br_cond =
  match pc_stack with
  | [] -> [(scope_id, br_cond, [])] 
  | stack -> (scope_id, br_cond, []) :: stack

let rec pc_after pc_stack scope_id =
  match pc_stack with
  | [] -> []
  | (sid, bc, pcs) :: stack' -> 
        if sid = scope_id
        then (sid, bc, pcs) :: pc_after stack' scope_id
        else pc_after stack' scope_id

let pc_collect_constr stack =
  List.fold_left
  (fun pclist (id, bc, pcs) -> bc :: (pcs @ pclist))
  [] stack

(** snapshot defintions *)
type snap =
  | Unit
  | Snap of symb_val
  | SnapPair of symb_val * symb_val

let snap_pair s1 s2 = SnapPair (s1, s2)

let snap_first s =
  match s with
  | Unit -> failwith "can't get first snapshot of unit snapshot" 
  | Snap s -> Snap s
  | SnapPair (s1, s2) -> Snap s1

let snap_second s =
  match s with
  | Unit -> failwith "can't get second of unit snapshot"
  | Snap s -> failwith "can't get second of single snapshot" 
  | SnapPair (s1, s2) -> Snap s2

(** heap elements and symbolic heap
  The symbolic maintains a multiset of heap chunks which are
  of the form obj(V, snap, [Id -> V]) or a predicate with an id
  and list of args.
  *)

type heap_chunk =
  | Obj of (ident * sort) * snap * symb_val IdMap.t
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
  {store = empty_store; pc=[]; heap=[]; old=[]}

let mk_symb_state st =
  {store=st; pc=[]; heap=[]; old=[]}

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
  IdMap.bindings s
  |> List.map (fun (k, v) -> (string_of_ident k) ^ ":" ^ (string_of_symb_val v))
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
  |> List.map (fun (pc, bc, vars) ->
      "(" ^ (string_of_ident pc) ^ ", " ^ (string_of_symb_val bc) ^ ", "
      ^ (string_of_pcset vars) ^ ")")
  |> String.concat ", "
  |> sprintf "[%s]"

let string_of_snap s =
  match s with
  | Unit -> "unit"
  | Snap ss -> string_of_symb_val ss 
  | SnapPair (s1, s2) ->
      sprintf "%s(%s)" (string_of_symb_val s1) (string_of_symb_val s2)

let string_of_hc chunk =
  match chunk with
  | Obj ((id, srt), snap, symb_fields) ->
    sprintf "Obj((Id:%s, Sort:%s), Snap:%s, Fields:%s)" (string_of_ident id)
      (string_of_sort srt) (string_of_snap snap) (string_of_symb_fields symb_fields)
  | Pred (id, symb_vals) -> sprintf "Pred(Id:%s, Args:%s)" (string_of_ident id)
      (string_of_symb_val_list symb_vals)

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
  sprintf "\n\tStore: %s,\n\tPCStack: %s\n\tHeap: %s\n\tOld: %s" store pc heap old

(** Entry point for the symbexec engine *)
let exec spl_prog prog proc =
  Debug.info (fun () ->
      "Checking procedure " ^ string_of_ident (name_of_proc proc) ^ "...\n");

  (** Extract sorts of formal params and havoc them into a fresh store. *)
  let formals = proc.proc_contract.contr_formals in
  let locs = proc.proc_contract.contr_locals in
  let formal_arg_terms =
    List.fold_left
      (fun term_lst var ->
        let srt = IdMap.find var locs in
        Var (var, srt.var_sort) :: term_lst)
      [] formals 
  in
  let init_state = mk_symb_state (havoc_terms empty_store formal_arg_terms) in
  Debug.debug(fun() ->
      sprintf "%sInitial State:\n{%s\n}\n\n"
      lineSep (string_of_state init_state)
  )

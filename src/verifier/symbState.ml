(** {5 Symbolic state primitives inspired by Viper's Silicon} *)

open Util
open Grass
open GrassUtil
open Prog
open Printf

exception NotYetImplemented of string
exception HeapChunkNotFound of string 
let todo str = raise (NotYetImplemented str)
exception SymbExecFail of string
let raise_err str = raise (SymbExecFail str)

(* symbolic val types, used to reconstruct terms and forms with
 * symbolic identifiers/vars *)
type symb_term = Symbt of term
type symb_form = Symbf of form 
type symb_sl_form = Symbslf of Sl.form 

let mk_symb_term t = Symbt t
let mk_symb_form f = Symbf f 

let term_of (Symbt t) = t
let form_of (Symbf f) = f 
let slform_of (Symbslf slf) = slf 

type symb_spec_form = 
  | SymbSL of symb_sl_form
  | SymbFOL of symb_form

type symb_spec = {
  symb_spec_form: symb_spec_form;
  spec_kind: spec_kind;
  spec_name: string;
  spec_msg: (ident -> (string * string)) option;
  spec_pos: source_position;
}

let mk_symb_spec sf k n m p = 
  {symb_spec_form=sf;
   spec_kind=k;
   spec_name=n;
   spec_msg=m;
   spec_pos=p}

(** Symbolic values *)
let mk_fresh_symb_var prefix srt = 
  let id = fresh_ident prefix in
  mk_symb_term (mk_var srt id)

let mk_fresh_symb_free_app srt id ts = mk_symb_term (mk_free_app srt id ts)

let ident_of_symb_val (id, _) = id 
let sort_of_symb_val (_, srt) = srt

let string_of_symb_term t =
  sprintf "%s" (string_of_term (term_of t))

let string_of_symb_terms ts =
  ts
  |> List.map (fun t -> string_of_symb_term t)
  |> String.concat ", "
  |> sprintf "[%s]"

let string_of_symb_form f =
  sprintf "%s" (string_of_form (form_of f))

let string_of_symb_sl_form f =
  sprintf "%s" (string_of_format pr_sl_form (slform_of f))

let equal_symb_vals (id1, srt1) (id2, srt2) = 
  if id1 = id2 && srt1 = srt2 
    then true else false

let string_of_symb_spec_form sf = 
  match sf with
  | SymbFOL sl -> (string_of_symb_form sl)
  | SymbSL sl -> (string_of_symb_sl_form sl)

let string_of_symb_spec_list specs =
  specs 
  |> List.map (fun sf -> string_of_symb_spec_form sf.symb_spec_form) 
  |> String.concat ", "
  |> sprintf "[%s]"

(** Helpers to format prints *)
let lineSep = "\n--------------------\n"

let string_of_symb_term_list vals =
  vals
  |> List.map (fun t -> (string_of_symb_term t))
  |> String.concat ", "
  |> sprintf "[%s]"

let string_of_symb_form_list fs =
  fs 
  |> List.map (fun v -> (string_of_symb_form v))
  |> String.concat ", "
  |> sprintf "[%s]"

let string_of_term_list ts =
  ts 
  |> List.map (fun v -> (string_of_term v))
  |> String.concat ", "
  |> sprintf "[%s]"

let string_of_ident_list ts =
  ts 
  |> List.map (fun v -> (string_of_ident v))
  |> String.concat ", "
  |> sprintf "[%s]"

let string_of_symb_store s =
  IdMap.bindings s
  |> List.map (fun (k, v) -> (string_of_ident k) ^ ":" ^ (string_of_symb_term v))
  |> String.concat ", "
  |> sprintf "{%s}"

let string_of_symb_val_map store =
  IdMap.bindings store
  |> List.map (fun (k, v) -> (string_of_ident k) ^ ":" ^ (string_of_symb_term v))
  |> String.concat ", "
  |> sprintf "{%s}"

let string_of_symb_fields fields =
  IdMap.bindings fields
  |> List.map (fun (k, v) -> (string_of_ident k) ^ ":" ^ (string_of_symb_term v))
  |> String.concat ", "
  |> sprintf "{%s}"

(** Symbolic store:
  maintains a mapping from grasshopper vars to symbolic vals
  ident -> term . *)
type symb_store = symb_term IdMap.t
let empty_store = IdMap.empty

let find_symb_val (store: symb_store) (id: ident) =
  Debug.debug(
    fun () ->
      sprintf "trying to find symbv for identifier %s\n"
      (string_of_ident id)
  );
  try IdMap.find id store
  with Not_found ->
    failwith ("find_symb_val: Could not find symbolic val for " ^ (string_of_ident id))

let maybe_find_symb_val (store: symb_store) (id: ident) = IdMap.find_opt id store

let find_or_make_symb_val (store: symb_store) (id: ident) srt =
  Debug.debug(
    fun () ->
      sprintf "trying to find symbv for identifier %s\n"
      (string_of_ident id)
  );
  try (store, IdMap.find id store)
  with Not_found ->
    let v = mk_fresh_symb_var "v" srt in
    (IdMap.add id v store, v)

(** havoc a list of terms into a symbolic store *)
let havoc symb_store terms =
  List.fold_left
    (fun sm term ->
      match term with
      | Var (id, srt) -> 
          let v = mk_fresh_symb_var "v" srt in
          IdMap.add id v sm
      | _ -> failwith "tried to havoc a term that isn't a Var")
    symb_store terms

let havoc_id symb_store id srt =
     let v = mk_fresh_symb_var "v" srt in
     IdMap.add id v symb_store

let merge_stores s1 s2 =
  IdMap.merge (fun k xo yo ->
    match xo,yo with
    | Some x, Some y -> Some y
    | _ -> None
  ) s1 s2

(** path condition (pc) stack
  A sequence of scopes a tuple of (scope id, branch condition, [V])
  list[V] is the list of path conditions.
  Note: scope identifiers are used to label branche conditions
    and path conds obtained from two points of program execution.
 *)

(** path condition chunks are of shape (scope id, branch cond, pc list)
 TODO: optimize symb_val list to use a set. *)
type pc_chunk = ident * form * form list
type pc_stack = pc_chunk list

let string_of_pcset s =
  s
  |> List.map (fun f -> (string_of_form f))
  |> String.concat ", "

let string_of_pc_stack pc =
  pc
  |> List.map (fun (id, bc, vars) ->
      "(" ^ (string_of_ident id) ^ ", " ^ (string_of_form bc) ^ ", "
      ^ "[" ^ (string_of_pcset vars) ^ "]" ^ ")")
  |> String.concat ", "
  |> sprintf "[%s]"

let pc_push_new (stack: pc_stack) scope_id br_cond =
  match stack with
  | [] -> [(scope_id, br_cond, [])]
  | stack ->
      let s = (scope_id, br_cond, []) :: stack in
      Debug.debug( fun() -> sprintf "pc_push_new %s\n" (string_of_pc_stack s));
      s
  
let rec pc_add_path_cond (stack: pc_stack) f =
  match stack with
  | [] -> 
      Debug.debug(fun () -> sprintf "pc_add_path_cond (%s)\n" (string_of_form f));
      let s = pc_push_new [] (fresh_ident "scope") (mk_true) in
      pc_add_path_cond s f
  | (sid, bc, pcs) :: stack' -> (sid, bc, f :: pcs) :: stack'

let pc_add_path_conds (stack: pc_stack) fs = 
  List.fold_left (fun pcs f -> 
    pc_add_path_cond pcs f)
  stack fs

let rec pc_after (pcs: pc_stack) scope_id =
  match pcs with
  | [] -> []
  | (sid, bc, pcs) :: stack' ->
    if sid = scope_id
    then (sid, bc, pcs) :: pc_after stack' scope_id
    else pc_after stack' scope_id

let pc_collect_constr (stack: pc_stack) =
  List.fold_left
  (fun pclist (id, bc, pcs) -> bc :: (pcs @ pclist))
  [] stack

(* Returns None if the entailment holds, otherwise Some (list of error messages, model) *)
(** carry over from Sid's SymbExec *)
let check_entail prog p1 p2 =
  if p1 = p2 || p2 = mk_true then None
  else (* Dump it to an SMT solver *)
    (** TODO: collect program axioms and add to symbolic state *)
    let p2 = Verifier.annotate_aux_msg "Related location" p2 in
    (* Close the formulas: assuming all free variables are existential *)
    let close f = smk_exists (Grass.IdSrtSet.elements (sorted_free_vars f)) f in
    let labels, f =
      smk_and [p1; mk_not p2] |> close |> nnf
      (* Add definitions of all referenced predicates and functions *)
      |> fun f -> f :: Verifier.pred_axioms prog
      (** TODO: Add axioms *)
      |> (fun fs -> smk_and fs)
      (* Add labels *)
      |> Verifier.add_labels
    in
    let name = fresh_ident "form" |> Grass.string_of_ident in
    Debug.debug (fun () ->
      sprintf "\n\nCalling prover with name %s\n" name);
    match Prover.get_model ~session_name:name f with
    | None -> None
    | Some model -> Some (Verifier.get_err_msg_from_labels model labels, model)

(** SMT solver calls *)
let check pc_stack prog v =
  match check_entail prog (smk_and (pc_collect_constr pc_stack)) v  with 
  | Some errs -> raise_err "SMT check failed"
  | None -> ()

(** Snapshot defintions *)
(** snapshot adt encoding for SMT solver *)
let snap_tree_id = fresh_ident "snap_tree" 
let tree_id = fresh_ident "tree" 
let emp_id = fresh_ident "emp" 
let first_id = fresh_ident "first" 
let second_id = fresh_ident "second" 

(*syntax, name of data type, list of constructors [constr], the constructors each take
 * a list of args, emp has [], tree two args for each constructor. *)
let snap_adt = (snap_tree_id,
  [(emp_id, []);
   (tree_id,
    [(first_id, FreeSrt snap_tree_id);
     (second_id, FreeSrt snap_tree_id)
    ])
  ])

let snap_typ = Adt (snap_tree_id, [snap_adt])

let snap_first snp =
  App (Destructor first_id, [snp], snap_typ)

let snap_second snp =
  App (Destructor second_id, [snp], snap_typ)

let emp_snap =
  App (Constructor emp_id, [], snap_typ)

let snap_pair s1 s2 =
  App (Constructor tree_id, [s1; s2], snap_typ) 

let fresh_snap_tree () =
  mk_free_const snap_typ (fresh_ident "fresh_snap")

let fresh_snap =
  App (Destructor tree_id, [snap_first (emp_snap); snap_second (emp_snap)], snap_typ)

(* snap is already a term *)

(** heap elements and symbolic heap
  The symbolic maintains a multiset of heap chunks which are
  of the form obj(term, snap, [Id -> V]) or a predicate with an id a
  snapshot and list of args.
  *)
type heap_chunk =
  | Obj of symb_term * term * symb_store
  | ObjForm of symb_form * term * symb_store
  | ObjPred of ident * term * symb_term list
  (*| Eps of symb_val * symb_val IdMap.t (* r.f := e *)*)

let mk_heap_chunk_obj t snp m =
  Obj (t, snp, m)

let mk_fresh_heap_chunk_obj t =
  mk_heap_chunk_obj t (emp_snap) empty_store

let mk_heap_chunk_obj_form f snp m =
  ObjForm (f, snp, m)

let mk_heap_chunk_obj_pred id snp vals  =
  ObjPred (id, snp, vals)

let get_pred_chunk_snap = function
  | ObjPred (_, snp, _) -> snp
  | _ -> failwith "other chunks don't carry a snapshot" 

let get_field_store = function
  | Obj (_, _, m) -> m
  | ObjForm (_, _, m) -> m
  | ObjPred (_, _, m) -> failwith "pred chunk doesn't carry a store" 

let add_to_heap_chunk_map hc k v =
  match hc with
  | Obj (t, snp, m) -> Obj (t, snp, IdMap.add k v m)
  | ObjForm (f, snp, m) -> ObjForm (f, snp, IdMap.add k v m)
  | ObjPred (_, _, _) as p -> p

let equal_field_maps fm1 fm2 =
  IdMap.equal (=) fm1 fm2

let equal_symb_val_lst vs1 vs2 =
  List.fold_left2 (fun acc v1 v2 ->
    acc && equal_symb_vals v1 v2)
  true vs1 vs2

let equal_heap_chunks c1 c2 = 
  match c1, c2 with 
  | Obj (t1, s1, sm1), Obj (t2, s2, sm2)
  when t1 = t2 && equal_field_maps sm1 sm2 -> true
  | ObjForm (f1, s1, sm1), ObjForm (f2, s2, sm2)
  when equal (form_of f1) (form_of f2) && equal_field_maps sm1 sm2 -> true
  | ObjPred (id1, s1, ts1), ObjPred(id2, s2, ts2)
  when id1 = id2 && ts1 = ts2 -> true
  | _ -> false

let string_of_hc chunk =
  match chunk with
  | Obj (t, snap, symb_fields) ->
    sprintf "Obj((term:%s, sort:%s), Snap:%s, Fields:%s)" (string_of_symb_term t)
    (string_of_sort (sort_of (term_of t))) (string_of_term snap) (string_of_symb_fields symb_fields)
  | ObjForm (f, snap, symb_fields) ->
    sprintf "ObjForm(%s, Snap:%s, Fields:%s)" (string_of_symb_form f)
      (string_of_term snap) (string_of_symb_fields symb_fields)
  | ObjPred (id, snap, ts) ->
    sprintf "ObjPred(%s, Snap:%s, terms:%s)" (string_of_ident id)
      (string_of_term snap) (string_of_symb_term_list ts)

type symb_heap = heap_chunk list

let heap_add h stack hchunk = (hchunk :: h, stack)

let rec heap_find_by_symb_term h t =
  match h with
  | [] -> raise (HeapChunkNotFound (sprintf "for id(%s) %s" (string_of_symb_term t) (string_of_sort (sort_of (term_of t)))))
  | Obj (tt, _, _) as c :: h' ->
      if tt = t then c else heap_find_by_symb_term h' t
  | ObjPred (id1, _, _) as c :: h' ->
      let id2 = free_symbols_term (term_of t) in
      if IdSet.mem id1 id2 then c else heap_find_by_symb_term h' t
  | _ :: h' -> heap_find_by_symb_term h' t

let rec heap_find_pred_chunk h id ts =
  match h with
  | [] -> raise (HeapChunkNotFound (sprintf "for ident (%s)" (string_of_ident id)))
  | ObjPred(id1, _, ts1) as p :: h'
    when id = id1 ->
      if id = id1 && ts = ts1 then
        p else heap_find_pred_chunk h' id ts
  | p :: h' -> heap_find_pred_chunk h' id ts

let rec heap_remove_by_term h t = 
  let chunk = heap_find_by_symb_term h (Symbt t) in
  (chunk, List.filter (fun hc ->
      match hc with
      | Obj (Symbt t1, _, _) ->
          if t1 = t then (Debug.debug (fun() -> sprintf "Dropping element\n"); false) else true
      | ObjPred (id1, _, _) ->
          let id2 = free_consts_term t in
          IdSet.mem id1 id2
      |_ -> true) h)

let heap_remove h stack hchunk = 
  List.filter (fun hc ->
    if equal_heap_chunks hchunk hc then
      match hchunk, hc with
      | Obj (Symbt t1, snp1, _), Obj (Symbt t2, snp2, _) ->
        check stack (empty_prog) (mk_eq t1 t2);
        false 
      | ObjForm (Symbf f1, snp1, _), ObjForm (Symbf f2, snp2, _) ->
        if equal f1 f2 then false else true
      | ObjPred (id1, snp1, ts1), ObjPred (id2, snp2, ts2) -> 
        if id1 = id2 && ts1 = ts2 && snp1 = snp2 then false else true 
      | _ -> true 
    else true) h

let string_of_heap h =
  h
  |> List.map (fun ele -> (string_of_hc ele))
  |> String.concat ", "
  |> sprintf "[%s]"

(** Symbolic State are records that are manipulated during execution:
  1. symbolic store; a mapping from variable names to symbolic values
  2. symbolic heap; records which locations, fields, access predicates are
     accessable along with symbolic values they carry.
  3. path condition stack; this carries all path conditions which are represnented
     as symbolic expressions.
 *)
type symb_state = {
    store: symb_store;
    old_store: symb_store;
    pc: pc_stack;
    heap: symb_heap;
    prog: program; (* need to carry around prog for prover check *)
    proc: proc_decl;
  }

let mk_symb_state st prog proc =
  { store=st;
    old_store=empty_store;
    pc=[];
    heap=[];
    prog=prog;
    proc=proc
  }

let update_store_prog state proc prog =
  { state with
    proc=proc;
    prog=prog;
  }

let update_store state store old_store =
  {state with store=store; old_store=old_store}

let update_pc state pcs =
  {state with pc=pcs}

let string_of_state s =
  let store = string_of_symb_store s.store in
  let old_store = string_of_symb_store s.old_store in
  let pc = string_of_pc_stack s.pc in
  let heap = string_of_heap s.heap in
  sprintf "\n\tStore: %s,\n\tOld Store: %s\n\tPCStack: %s\n\tHeap: %s" store old_store pc heap

let string_of_states ss =
  ss
  |> List.map (fun s -> (string_of_state s))
  |> String.concat ", "
  |> sprintf "[%s]"

let merge_lsts h1 h2 =
  match h1, h2 with
  | [], [] -> []
  | [], x -> x 
  | x, [] -> x
  | x, y -> x @ y

let merge_states s1 s2 = 
 { store=s1.store;
   old_store=s1.old_store;
   heap=merge_lsts s1.heap s2.heap;
   pc=merge_lsts s1.pc s2.pc;
   prog=s1.prog (* programs are the same *);
   proc=s1.proc (* procs are the same *);
 }

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

(** Symbolic values *)
type symb_val = ident * sort

let mk_symb_val name srt = (mk_ident name, srt)
let mk_symb_val_ident id srt = (id, srt)
let mk_fresh_symb_val prefix srt = 
  let id = fresh_ident prefix in
  mk_symb_val_ident id srt

let mk_fresh_symb_var name srt =
  let v, _ = mk_fresh_symb_val "v" srt in
  (Var (v, srt))

let ident_of_symb_val (id, _) = id 
let sort_of_symb_val (_, srt) = srt

let string_of_symb_val (id, srt) =
  sprintf "%s:(%s)\n" (string_of_ident id) (string_of_sort srt)

let equal_symb_vals (id1, srt1) (id2, srt2) = 
  if id1 = id2 && srt1 = srt2 
    then true else false

(** Helpers to format prints *)
let lineSep = "\n--------------------\n"

let string_of_symb_val_list vals =
  vals
  |> List.map (fun v -> (string_of_symb_val v))
  |> String.concat ", "
  |> sprintf "[%s]"

let string_of_form_list fs =
  fs 
  |> List.map (fun v -> (string_of_form v))
  |> String.concat ", "
  |> sprintf "[%s]"

let string_of_symb_store s =
  IdMap.bindings s
  |> List.map (fun (k, v) -> (string_of_ident k) ^ ":" ^ (string_of_term v))
  |> String.concat ", "
  |> sprintf "{%s}"

let string_of_symb_val_map store =
  IdMap.bindings store
  |> List.map (fun (k, v) -> (string_of_ident k) ^ ":" ^ (string_of_symb_val v))
  |> String.concat ", "
  |> sprintf "{%s}"

let string_of_symb_fields fields =
  IdMap.bindings fields
  |> List.map (fun (k, v) -> (string_of_ident k) ^ ":" ^ (string_of_term v))
  |> String.concat ", "
  |> sprintf "{%s}"

(** Symbolic store:
  maintains a mapping from grasshopper vars to symbolic vals
  ident -> symb_val . *)
type symb_store = term IdMap.t
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

(** havoc a list of terms into a symbolic store *)
let havoc symb_store terms =
  List.fold_left
    (fun sm term ->
      match term with
      | Var (id, srt) -> 
          let (v, srt2) = mk_fresh_symb_val "v" srt in
          IdMap.add id (Var (v, srt2)) sm
      | _ -> failwith "tried to havoc a term that isn't a Var")
    symb_store terms

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
type snap =
  | Unit 
  | Snap of term 
  | SnapPair of snap * snap 

let snap_pair s1 s2 = SnapPair (s1, s2)

let snap_first s =
  match s with
  | Unit -> Unit
  | Snap s -> Snap s
  | SnapPair (s1, s2) -> s1

let snap_second s =
  match s with
  | Unit -> Unit
  | Snap s -> Snap s
  | SnapPair (s1, s2) -> s2

let term_of_snap = function
  | Unit -> Var (("unit", 0), Bool)
  | Snap t -> t
  | SnapPair (_, _) -> todo "term_of_snap SnapPair"

let rec equal_snaps s1 s2 =
  match s1, s2 with
  | Unit, Unit -> true
  | Unit, Snap ss2 | Snap ss2, Unit -> false
  | Snap s1, Snap s2 -> if s1 = s2 then true else false
  | SnapPair (l1, r1), SnapPair (l2, r2) ->
      equal_snaps l1 r1 && equal_snaps l2 r2
  | _ -> false

let mk_fresh_snap srt = 
  let (v, _) = mk_fresh_symb_val "snap" srt in
  Snap (Var (v, srt))

(** snapshot adt encoding for SMT solver *)
let snap_adt = (("snap_tree", 0),
  [(("emp", 0), []);
   (("tree", 0),
    [(("fst", 0), FreeSrt ("snap_tree", 0));
     (("snd", 0), FreeSrt ("snap_tree", 0))
    ])
  ])

let snap_typ = Adt (("snap_tree", 0), [snap_adt])

let rec string_of_snap s =
  match s with
  | Unit -> "unit[snap]"
  | Snap ss -> string_of_term ss
  | SnapPair (s1, s2) ->
      sprintf "%s(%s)" (string_of_snap s1) (string_of_snap s2)

(** heap elements and symbolic heap
  The symbolic maintains a multiset of heap chunks which are
  of the form obj(term, snap, [Id -> V]) or a predicate with an id
  and list of args.
  *)
type heap_chunk =
  | Obj of term * snap * symb_store
  | ObjForm of form * snap * symb_store
  (*| Eps of symb_val * symb_val IdMap.t (* r.f := e *)
  | Pred of ident * snap * symb_val list*)

let mk_heap_chunk_obj t snp m =
  Obj (t, snp, m)

let mk_fresh_heap_chunk_obj t =
  mk_heap_chunk_obj t Unit empty_store

let mk_heap_chunk_obj_form f snp m =
  ObjForm (f, snp, m)

let get_field_store = function
  | Obj (_, _, m) -> m
  | ObjForm (_, _, m) -> m

let add_to_heap_chunk_map hc k v =
  match hc with
  | Obj (t, snp, m) -> Obj (t, snp, IdMap.add k v m)
  | ObjForm (f, snp, m) -> ObjForm (f, snp, IdMap.add k v m)

let equal_field_maps fm1 fm2 =
  IdMap.equal (=) fm1 fm2

let equal_symb_val_lst vs1 vs2 =
  List.fold_left2 (fun acc v1 v2 ->
    acc && equal_symb_vals v1 v2)
  true vs1 vs2

let equal_heap_chunks c1 c2 = 
  match c1, c2 with 
  | Obj (t1, s1, sm1), Obj (t2, s2, sm2)
  when t1 = t2 && equal_field_maps sm1 sm2 -> 
    equal_snaps s1 s2
  | ObjForm (f1, s1, sm1), ObjForm (f2, s2, sm2)
  when equal f1 f2 && equal_field_maps sm1 sm2 ->
    equal_snaps s1 s2
  | _ -> false

let string_of_hc chunk =
  match chunk with
  | Obj (t, snap, symb_fields) ->
    sprintf "Obj((term:%s, sort:%s), Snap:%s, Fields:%s)" (string_of_term t)
    (string_of_sort (sort_of t)) (string_of_snap snap) (string_of_symb_fields symb_fields)
  | ObjForm (f, snap, symb_fields) ->
    sprintf "ObjForm(%s, Snap:%s, Fields:%s)" (string_of_form f)
      (string_of_snap snap) (string_of_symb_fields symb_fields)

type symb_heap = heap_chunk list

let heap_add h stack hchunk = (hchunk :: h, stack)

let rec heap_find_by_term h t =
  match h with
  | [] -> raise (HeapChunkNotFound (sprintf "for id(%s)" (string_of_term t)))
  | Obj (tt, _, _) as c :: h' ->
      Debug.debug(fun() -> sprintf "check: (%s), (%s) == target:(%s)\n" (string_of_hc c) (string_of_sort (sort_of tt)) (string_of_term t));
      if tt = t then c else heap_find_by_term h' t
  | _ :: h' -> heap_find_by_term h' t

let rec heap_find_by_chunk h hc = 
  match h with
  | [] -> raise (HeapChunkNotFound (sprintf "for symb_val (%s)" (string_of_hc hc)))
  | Obj (_,_,_) as c :: h' ->
      Debug.debug(fun() -> sprintf "check: (%s) == (%s)\n" (string_of_hc c) (string_of_hc hc));
      if equal_heap_chunks c hc then 
        c else heap_find_by_chunk h' hc 
  | ObjForm (_,_,_) as f :: h' ->
      Debug.debug(fun() -> sprintf "check: (%s) == (%s)\n" (string_of_hc f) (string_of_hc hc));
      if equal_heap_chunks f hc then
        f else heap_find_by_chunk h' hc 

let rec heap_find_by_form h f = 
  match h with
  | [] -> raise (HeapChunkNotFound (sprintf "for id(%s)" (string_of_form f)))
  | ObjForm (ff, _, _) as fc :: h' -> if equal ff f then fc else heap_find_by_form h' f 
  | _ :: h'-> heap_find_by_form h' f 

let rec heap_remove_by_term h t = 
  List.filter (fun hc ->
    match hc with
    | Obj (t1, _, _) as c ->
        Debug.debug(fun() -> sprintf "check: (%s), (%s) == target:(%s)\n" (string_of_hc c) (string_of_sort (sort_of t)) (string_of_term t));
        if t1 = t then (Debug.debug (fun() -> sprintf "Dropping element\n"); false) else true
    |_ -> true) h

let heap_remove h stack hchunk = 
  List.filter (fun hc ->
    if equal_heap_chunks hchunk hc then
      match hchunk, hc with
      | Obj (t1, snp1, _), Obj (t2, snp2, _) ->
        check stack (empty_prog) (mk_eq t1 t2);
        false 
      | ObjForm (f1, snp1, _), ObjForm (f2, snp2, _) ->
        if equal f1 f2 then false else true
      |_ -> true
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
  }

let mk_symb_state st prog =
  {store=st; old_store=empty_store; pc=[]; heap=[]; prog=prog}

let mk_empty_state = 
  {store=empty_store; old_store=empty_store; pc=[]; heap=[]; prog=empty_prog}

let update_store state store =
  {state with store=store}

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
 {store=s1.store;
   old_store=s1.old_store;
   heap=merge_lsts s1.heap s2.heap;
   pc=merge_lsts s1.pc s2.pc;
   prog=s1.prog (* programs are the same *)}

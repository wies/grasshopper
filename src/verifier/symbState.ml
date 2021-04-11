(** {5 Symbolic state primitives inspired by Viper's Silicon} *)

open Util
open Grass
open GrassUtil
open Prog
open Axioms 
open Printf

exception NotYetImplemented of string
exception HeapChunkNotFound of string 
let todo str = raise (NotYetImplemented str)
exception SymbExecFail of string
let raise_err str = raise (SymbExecFail str)

(** Symbolic values *)
let mk_fresh_symb_var prefix srt = 
  mk_var srt (fresh_ident prefix) 

let mk_fresh_symb_free_app srt id ts = mk_free_app srt id ts

let ident_of_symb_val (id, _) = id 
let sort_of_symb_val (_, srt) = srt

let string_of_terms ts =
  ts
  |> List.map (fun t -> string_of_term t)
  |> String.concat ", "
  |> sprintf "[%s]"

let equal_symb_vals (id1, srt1) (id2, srt2) = 
  if id1 = id2 && srt1 = srt2 
    then true else false

(** Helpers to format prints *)
let lineSep = "\n--------------------\n"

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
  |> List.map (fun (k, v) -> (string_of_ident k) ^ ":" ^ (string_of_term v))
  |> String.concat ", "
  |> sprintf "{%s}"

let string_of_symb_val_map store =
  IdMap.bindings store
  |> List.map (fun (k, v) -> (string_of_ident k) ^ ":" ^ (string_of_term v))
  |> String.concat ", "
  |> sprintf "{%s}"

let string_of_idset s =
  IdSet.elements s
  |> List.map (fun e -> string_of_ident e)
  |> String.concat ", "
  |> sprintf "[%s]"

(** Symbolic store:
  maintains a mapping from grasshopper vars to symbolic vals
  ident -> term . *)
type symb_store = term IdMap.t
let empty_store = IdMap.empty

let find_symb_val (store: symb_store) (id: ident) =
  try IdMap.find id store
  with Not_found ->
    failwith ("find_symb_val: Could not find symbolic val for " ^ (string_of_ident id))

let maybe_find_symb_val (store: symb_store) t = 
  let rec get_t = function
    | Var (id, _) ->
       IdMap.find_opt id store |> Opt.get_or_else t
    | App (sym, ts, srt) -> App (sym, List.map get_t ts, srt)
  in
  get_t t

let find_or_make_symb_val (store: symb_store) (id: ident) srt =
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

(* heap elements and symbolic heap *)
type heap_chunk =
  | Obj of ident * term * term (* r.id -> (field id, r (term), snapshot) *)
  | ObjPred of ident * term list * term (* id, args, snapshot *)

let mk_heap_chunk_obj field_id rcvr snp =
  Obj (field_id, rcvr, snp)

let mk_fresh_heap_chunk_obj field_id rcvr =
  mk_heap_chunk_obj field_id rcvr (emp_snap)

let mk_heap_chunk_obj_pred id args snp = 
  ObjPred (id, args, snp)

let get_heap_chunk_snap = function
  | Obj (_, _, snp) -> snp
  | ObjPred (_, _, snp) -> snp

let equal_term_lst ts1 ts2 =
  List.fold_left2 (fun acc t1 t2 ->
    acc && t1 = t2)
  true ts1 ts2

let string_of_hc chunk =
  match chunk with
  | Obj (id, rcvr, snp) ->
    sprintf "Obj(fld:%s, rcvr:%s, snp:%s)" (string_of_ident id) (string_of_term rcvr) (string_of_term snp)
  | ObjPred (id, args, snp) ->
    sprintf "ObjPred(%s, args:%s, snp:%s)" (string_of_ident id)
      (string_of_term snp) (string_of_term_list args)

type symb_heap = heap_chunk list

let heap_add h stack hchunk = (hchunk :: h, stack)

(* axioms for snapshot reads *)
let f_snap_id = mk_name_generator "f_snap"
let f_snap_inv_id = mk_name_generator "f_inv_snap"
let f_snp_loc_srt_id struct_srt = f_snap_id struct_srt
let f_snp_loc_srt_inv_id struct_srt = f_snap_inv_id struct_srt 

let mk_f_snap srt snp = 
  mk_free_fun srt (f_snp_loc_srt_id srt) [snp]

let snap_axiom srt =
  let x = mk_ident "x" in
  let xvar = mk_var snap_typ x in
  let f = mk_f_snap srt xvar in
  let finv_app = mk_app snap_typ (FreeSym (f_snp_loc_srt_inv_id srt)) [f] in
  
  let f_inj = mk_eq finv_app xvar in
  let name, _ = (f_snp_loc_srt_id srt) in
  let f_app_gen = ([Match (f, [])], [finv_app]) in

  let axiom = mk_axiom ~gen:[f_app_gen] ("snap_axiom_" ^ name) (mk_forall [x, snap_typ] f_inj) in
  Debug.debug (fun () -> sprintf "snap_axiom (%s)\n" (string_of_form axiom));
  axiom

let get_map_range_sort srt = 
  match srt with
  | Map ([Loc _], ran_srt) -> ran_srt
  | _ -> failwith "illtyped sort" 

let snapshot_axioms prog =
  (* rather fold over the global var decls, and pattern match Map<Loc<T1>, T2> extract T2. *)
  IdMap.fold (fun _ var axioms -> 
    match var.var_sort with
    | Map ([Loc _], rsrt) -> snap_axiom rsrt :: axioms
    | _ -> axioms) prog.prog_vars []

let mk_and_args args1 args2 = 
  List.combine args1 args2
  |> List.map (fun (t1, t2) -> mk_eq t1 t2)
  |> smk_and

(* Returns None if the entailment holds, otherwise Some (list of error messages, model) *)
(** carry over from Sid's SymbExec *)
let check_entail prog p1 p2 =
  let snap_axioms = snapshot_axioms prog in
  if p1 = p2 || p2 = mk_true then None
  else (* Dump it to an SMT solver *)
    (** TODO: collect program axioms and add to symbolic state *)
    let p2 = Verifier.annotate_aux_msg "Related location" p2 in
    (* Close the formulas: assuming all free variables are existential *)
    let close f = smk_exists (Grass.IdSrtSet.elements (sorted_free_vars f)) f in
    let prog2 = { prog with prog_preds = IdMap.empty } in
    let labels, f =
      smk_and [p1; mk_not p2] |> close |> nnf
      (* Add definitions of all referenced predicates and functions *)
      |> fun f -> f :: Verifier.pred_axioms prog2 
      (** TODO: Add axioms *)
      |> (fun fs -> smk_and (fs @ snap_axioms))
      (* Add labels *)
      |> Verifier.add_labels
    in
    let name = fresh_ident "form" |> Grass.string_of_ident in
    Debug.debug (fun () ->
      sprintf "\n\nCalling prover with name %s\n" name);
    Debug.debug(fun () -> sprintf "FORM Before SMT (%s) \n" (string_of_form f));
    match Prover.get_model ~session_name:name f with
    | None -> None
    | Some model -> Some (Verifier.get_err_msg_from_labels model labels, model)

(** SMT solver calls *)
let check pc_stack prog v =
  match check_entail prog (smk_and (pc_collect_constr pc_stack)) v  with 
  | Some errs -> raise_err "SMT check failed"
  | None -> ()

let check_bool pc_stack prog v =
  match check_entail prog (smk_and (pc_collect_constr pc_stack)) v with
  | Some errs -> false
  | None -> true

let equal_heap_chunks stack c1 c2 =
  let equal_terms t =
    check_bool stack (empty_prog) t 
  in
  match c1, c2 with 
  | Obj (id1, _, s1), Obj (id2, _, s2)
  when id1 = id2 && equal_terms (mk_eq s1 s2) -> true
  | ObjPred (id1, args1, s1), ObjPred(id2, args2, s2)
  when id1 = id2 && equal_terms (mk_eq s1 s2) && equal_term_lst args1 args2 -> true
  | _ -> false

let rec heap_find_pred_chunk stack h id args =
  match h with
  | [] -> raise (HeapChunkNotFound (sprintf "for ident (%s)" (string_of_ident id)))
  | ObjPred(id1, args1, ts1) as p :: h'
    when id = id1 ->
      let ts_conj = mk_and_args args1 args in
      if (check_bool stack (empty_prog) ts_conj) then
        p else heap_find_pred_chunk stack h' id args 
  | p :: h' -> heap_find_pred_chunk stack h' id args 

let heap_remove h stack hchunk = 
  List.filter (fun hc ->
    (match hchunk, hc with
      | Obj (id1, fld1, s1), Obj (id2, fld2, s2) ->
          if id1 = id2 && fld1 = fld2 && (check_bool stack (empty_prog) (mk_eq s1 s2)) then false else true
      | ObjPred (id1, args1, snp1), ObjPred (id2, args2, snp2) -> 
        if id1 = id2 &&
          (check_bool stack (empty_prog) (mk_eq snp1 snp2)) then false else true
      | _ -> true)) h

let rec heap_find_by_symb_term stack h t =
  match h with
  | [] -> raise (HeapChunkNotFound (sprintf "for id(%s) %s" (string_of_term t) (string_of_sort (sort_of t))))
  | Obj (obj, id, tt) as c :: h' ->
      if (check_bool stack (empty_prog) (mk_eq tt t)) then c else heap_find_by_symb_term stack h' t
  | ObjPred (id1, _, _) as c :: h' ->
      let id2 = free_symbols_term t in
      if IdSet.mem id1 id2 then c else heap_find_by_symb_term stack h' t

let rec heap_find_by_field_id stack h prog receiver_term fldId =
  match h with
  | [] -> raise (HeapChunkNotFound (sprintf "for %s(%s) %s" (string_of_ident fldId) (string_of_term receiver_term) (string_of_sort (sort_of receiver_term))))
  | Obj (field_id, rcvr, tt) as c :: h' ->
      Debug.debug (fun () -> sprintf "Sort of receiver term (%s)\n" (string_of_sort (sort_of receiver_term)));
      Debug.debug (fun () -> sprintf "receiver term (%s)\n" (string_of_term receiver_term));
      Debug.debug (fun () -> sprintf "Sort of receiver hc term (%s)\n" (string_of_sort (sort_of rcvr)));
      Debug.debug (fun () -> sprintf "receiver rcvr (%s)\n" (string_of_term rcvr));
      Debug.debug (fun () -> sprintf "Sort of snap term (%s)\n" (string_of_sort (sort_of tt)));
      if field_id = fldId && (check_bool stack prog (mk_eq rcvr (receiver_term))) then c else heap_find_by_field_id stack h' prog receiver_term fldId
  | _ :: h' ->
       heap_find_by_field_id stack h' prog receiver_term fldId

let rec heap_remove_by_term stack h t =
  let chunk = heap_find_by_symb_term stack h t in
  (chunk, List.filter (fun hc ->
      match hc with
      | Obj (_, _, t1) ->
          if (check_bool stack (empty_prog) (mk_eq t1 t)) then (Debug.debug (fun() -> sprintf "Dropping element\n"); false) else true
      | ObjPred (id1, _, _) ->
          let id2 = free_consts_term t in
          IdSet.mem id1 id2) h)

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
    contract: contract;
  }

let mk_symb_state st prog contract =
  { store=st;
    old_store=empty_store;
    pc=[];
    heap=[];
    prog=prog;
    contract=contract
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
   contract=s1.contract (* procs are the same *);
 }

(** {5 Symbolic state primitives inspired by Viper's Silicon} *)

open Stdlib
open Util
open Grass
open GrassUtil
open Prog
open Axioms 
open Printf

exception NotYetImplemented of string
exception HeapChunkNotFound of string 
let todo str = Error str
exception SymbExecFail of string
let raise_err str = Error str

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

let string_of_forms fs =
  fs
  |> List.map (fun f -> string_of_form f)
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

(** Verification result type. *)
(* first indicates a successful verification, the second indicates an error and carries a message. *)
(* try passing the state in ok *)
type res =
  | Forms of form list
  | PCList of  pc_chunk list * term

type vresult = (res, string) Result.t 

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

let pc_push_new (stack: pc_stack) scope_id br_cond = (scope_id, br_cond, []) :: stack
  
let rec pc_add_path_cond (stack: pc_stack) f =
  match stack with
  | [] -> 
      Debug.debug(fun () -> sprintf "pc_add_path_cond (%s)\n" (string_of_form f));
      ((fresh_ident "scope"), (mk_true), [f]) :: stack
  | (sid, bc, pcs) :: stack' -> (sid, bc, f :: pcs) :: stack'

let pc_add_path_conds (stack: pc_stack) fs = 
  List.fold_left (fun pcs f -> 
    pc_add_path_cond pcs f)
  stack fs

let rec pc_after (pcs: pc_stack) scope_id =
  let rec f acc scope_id l =
    match l with
    | [] -> [] 
    | (sid, bc, pcs) :: t ->
        let l = (sid, bc, pcs) :: acc in
        if sid = scope_id then List.rev l 
        else f l scope_id t 
  in f [] scope_id pcs
      
let pc_collect_constr (stack: pc_stack) =
  List.fold_left
  (fun pclist (id, bc, pcs) -> bc :: (pcs @ pclist))
  [] stack

let rec diff_stacks pc1 pc2 =
  List.filter (fun x -> not (List.mem x pc2)) pc1

(*let postcond_stack =
    diff_stacks (pc_of_chunk (List.hd state.pc)) (pc_of_chunk (List.hd state_precond.pc))
  in
  *)

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
  (*
  match s2 with
  | App (Constructor c, [], snap_typ) when c = emp_id -> s1
  | _ -> App (Constructor tree_id, [s1; s2], snap_typ)  
  *)
  App (Constructor tree_id, [s1; s2], snap_typ)  

let fresh_snap_tree () =
  mk_var snap_typ (fresh_ident "fresh_snap")

let fresh_snap =
  App (Destructor tree_id, [snap_first (emp_snap); snap_second (emp_snap)], snap_typ)

(* snap is already a term *)

(* heap elements and symbolic heap *)
type heap_chunk =
  | Obj of ident * term * term (* r.id -> (field id, r (term), snapshot) *)
  | ObjPred of ident * term list * term (* id, args, snapshot *)

let field_of_hc = function
  | Obj (id, _, _)
  | ObjPred (id, _, _) -> id

let rcvr_of_hc = function
  | Obj (_, t, _) -> t
  | _ -> failwith "can only call on Obj" 

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
      (string_of_term_list args) (string_of_term snp) 

type symb_heap = heap_chunk list

let heap_add h stack hchunk = (hchunk :: h, stack)

let rec remove_snaps f = 
    let fvs = sorted_free_vars f in 
    List.exists (fun (id, srt) -> 
        Debug.debug(fun () -> sprintf "ID %s\n" (string_of_ident id));
        Debug.debug(fun () -> sprintf "srt %s\n" (string_of_sort srt));
        Debug.debug(fun () -> sprintf "srt = snap_typ %b\n" (srt = snap_typ));
        srt = snap_typ
      ) (IdSrtSet.elements fvs)

 let rec remove_snaps_2 f= 
   match f with
   | Atom (App (Eq, [t1; t2], srt), _) -> 
       if (sort_of t1) = snap_typ && t2 = emp_snap 
       then true
       else false
   | _ -> false
 
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

let spec_forms_to_forms =
  Util.flat_map 
    (fun sf -> 
      let name = 
        Printf.sprintf "%s_%d_%d" 
          sf.spec_name sf.spec_pos.sp_start_line sf.spec_pos.sp_start_col
      in
      match sf.spec_form with
      | FOL f ->
          let f1 = f |> mk_name name in
          [f1]
      | SL _ -> [])

let rec mk_bool_form t =
 let trans_terms ts = 
       List.map (fun t -> mk_bool_form t) ts 
 in
 let op_form = function
   | AndTerm -> And
   | OrTerm -> Or
   | NotTerm -> Not
   | _ -> failwith "only convert for And/Or/Not"
 in
 match t with
 | App((AndTerm | OrTerm | NotTerm) as op, ts, _) 
     -> BoolOp(op_form op, trans_terms ts)
 | t -> Atom(t, [])

let cart_prod f l1 l2 = 
  let p = List.fold_left (fun acc x ->
    List.fold_left (fun acc2 z ->
      (f x z) :: acc2) acc l2)
  [] l1
  in
  List.rev p

let rec translate_ite f =
  (* translates terms into nested lists of pairs*)
  let rec terms_to_fpairs = function
    | App(FreeSym id, [t], srt) ->
       let plst1 = terms_to_fpairs t in
       let l3 = cart_prod (fun x y ->
         ((fst x) @ (fst y), [snd x; snd y]))
          plst1 [] 
       in 
       (* push the outer app into the second part of each pair*)
       List.map (fun (cnds, tt) -> (cnds, App(FreeSym id, tt, srt))) l3
    | Var (_, _) | App(Undefined, [], _) | App(IntConst _, [], _)
    | App(BoolConst _, [], _) | App(Eq, [], _)
    | App(FreeSym _, _, _) | App(Destructor _, _, _) 
    | App(Constructor _, _, _) as t -> [([], t)]
    | App(Eq, [t1; t2], srt) ->
       let plst1 = terms_to_fpairs t1 in
       let plst2 = terms_to_fpairs t2 in 
       let l3 = cart_prod (fun x y ->
         ((fst x) @ (fst y), [snd x; snd y]))
         plst1 plst2
       in 
       (* push the outer app into the second part of each pair*)
       List.map (fun (cnds, tt) -> (cnds, App(Eq, tt, srt))) l3
    | App(op, [t1; t2], srt) -> 
       let plst1 = terms_to_fpairs t1 in
       let plst2 = terms_to_fpairs t2 in 
       let l3 = cart_prod (fun x y ->
         ((fst x) @ (fst y), [snd x; snd y]))
         plst1 plst2
       in 
       (* push the outer app into the second part of each pair*)
       List.map (fun (cnds, tt) -> (cnds, App(op, tt, srt))) l3
    | App(Ite, [cond; t1; t2], srt) ->
        let plst1 = terms_to_fpairs t1 in
        let plst2 = terms_to_fpairs t2 in
        let l1 = List.map (fun (cnd, t) ->
          (mk_bool_form cond :: cnd, t))
          plst1
        in
        let l2 = List.map (fun (cnd, t) ->
          (mk_not (mk_bool_form cond) :: cnd, t))
          plst2
        in
        l1 @ l2
    | App(sym, ts, srt) ->
       let plst1 = List.map (fun t -> terms_to_fpairs t) ts in
       let fg = (fun x y ->
         ((fst x) @ (fst y), snd x @ [snd y]))
       in
       let l1 = List.fold_left (fun acc l ->
         cart_prod fg acc l)
       [([],[])] plst1
       in
       (* push the outer app into the second part of each pair*)
       List.map (fun (cnds, tt) -> (cnds, App(sym, tt, srt))) l1
  in
  let rec ff = function
    | Atom (t, a) -> 
        let plst = terms_to_fpairs t in
        let frms =List.map(fun c -> 
          let cnjts = mk_and (fst c) in
          mk_implies cnjts (Atom(snd c, a))) plst
        in
        mk_and frms
    | BoolOp (op, fs) -> BoolOp (op, List.map ff fs)
    | Binder (b, bvs, f, a) -> Binder (b, bvs, ff f, a)
  in
  ff f

let rec all_pairs h =
  match h with
  | [] -> []
  | h' :: hs ->
      let res = List.fold_left
        (fun acc hc ->
          (h', hc) :: acc)
        [] hs
      in
      res @ all_pairs hs

let infer_diseq heap stack =
  (* consider filtering out objPreds in the heap *)
  let m = List.fold_left
    (fun m hc ->
      let t = rcvr_of_hc hc in
      let fld_id = field_of_hc hc in
      let lst = IdMap.find_opt fld_id m in
      match lst with
      | Some l -> IdMap.add fld_id (t :: l) m
      | None -> IdMap.add fld_id [t] m)
    IdMap.empty (List.filter
      (fun hc -> 
        match hc with
        | Obj (_, _, _) -> true
        | ObjPred (_, _, _) -> false)  
      heap)
  in
  IdMap.fold (fun _ lst acc ->
    if List.length lst > 1 then
      let pairs = all_pairs lst in
      List.fold_left (fun acc p ->
        let f = mk_not (mk_eq (fst p) (snd p)) in 
        pc_add_path_cond acc f)
      acc pairs
    else
      acc)
  m stack

(* Returns None if the entailment holds, otherwise Some (list of error messages, model) *)
(** carry over from Sid's SymbExec *)
let check_entail prog p1 p2 =
  let snap_axioms = snapshot_axioms prog in
  let fun_axioms = spec_forms_to_forms prog.prog_axioms in
  let _ = List.iter (fun f -> Printf.printf "**** axioms (%s)\n" (string_of_form f)) fun_axioms in
  if p1 = p2 || p2 = mk_true then Result.Ok () 
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
      |> (fun fs -> smk_and (fs @ snap_axioms @ fun_axioms))
      |> (fun f -> Debug.debug(fun () -> sprintf "form before ite FOO %s\n" (string_of_form f)); f)
      |> translate_ite 
      (* possibly call nnf again*)
      (* Add labels *)
      |> Verifier.add_labels
    in
    let name = fresh_ident "form" |> Grass.string_of_ident in
    Debug.debug (fun () ->
      sprintf "\n\nCalling prover with name %s\n" name);
    Debug.debug(fun () -> sprintf "FORM Before SMT (%s) \n" (string_of_form f));
    match Prover.get_model ~session_name:name f with
    | None  -> Result.Ok () 
    | Some model ->
        Debug.debug (fun () -> sprintf "FAIL\n");
        Result.Error (Verifier.get_err_msg_from_labels model labels, model)

(** SMT solver calls *)
let check pc_stack prog v =
  match check_entail prog (smk_and (pc_collect_constr pc_stack)) v  with 
  | Result.Error err -> raise_err "SMT check failed"
  | Result.Ok _ -> Result.Ok ()

let check_bool pc_stack prog v =
  match check_entail prog (smk_and (pc_collect_constr pc_stack)) v with
  | Result.Error errs -> false
  | Result.Ok _ -> true

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
      if check_bool stack (empty_prog) ts_conj then
        p else heap_find_pred_chunk stack h' id args 
  | p :: h' -> heap_find_pred_chunk stack h' id args 

let heap_remove h stack hchunk = 
  List.filter (fun hc ->
    (match hchunk, hc with
      | Obj (id1, fld1, s1), Obj (id2, fld2, s2) ->
          if id1 = id2 && fld1 = fld2 && check_bool stack (empty_prog) (mk_eq s1 s2) then false else true
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
    old_heap: symb_heap;
    pc: pc_stack;
    heap: symb_heap;
    prog: program; (* need to carry around prog for prover check *)
    contract: contract;
    qvs: term list;
    visited_preds: ident list;
    join_fn: term option;
  }

let mk_symb_state st prog contract =
  { store=st;
    old_heap=[];
    pc=[];
    heap=[];
    prog=prog;
    contract=contract;
    qvs=[];
    visited_preds=[];
    join_fn=None;
  }

let incr_pred_cycle state id =
  {state with visited_preds=id :: state.visited_preds}

let rem_pred_cycle state id =
  {state with
   visited_preds=(List.filter
    (fun i -> i != id)
    state.visited_preds)
  }

let count_cycles state =
  List.fold_left
    (fun acc _ -> acc + 1)
    0
    state.visited_preds

let update_store state store old_heap =
  {state with store=store; old_heap=old_heap}

let update_pc state pcs =
  {state with pc=pcs}

let update_pc_stack state pcstack : pc_chunk =
  let (sid, brid, _) = List.hd state.pc in
  (sid, brid, pcstack)

let string_of_state s =
  let store = string_of_symb_store s.store in
  let old_heap= string_of_heap s.old_heap in
  let pc = string_of_pc_stack s.pc in
  let heap = string_of_heap s.heap in
  sprintf "\n\tStore: %s\n\tPCStack: %s\n\tHeap: %s\n\tOld Heap: %s" store pc heap old_heap 

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
   heap=merge_lsts s1.heap s2.heap;
   old_heap=s1.old_heap;
   pc=merge_lsts s1.pc s2.pc;
   prog=s1.prog (* programs are the same *);
   contract=s1.contract (* procs are the same *);
   qvs=merge_lsts s1.qvs s2.qvs;
   visited_preds=s1.visited_preds @ s2.visited_preds;
   join_fn=s1.join_fn;
 }

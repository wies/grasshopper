open Form
open FormUtil
open Axioms
open SimpleLanguage
open Entails

let unify_subst sig1 sig2 subst1 subst2 =
  let cstr_for tpe id1 id2 =
    let f = match tpe with
      | Some (Bool) ->
        failwith "TODO: args of pred ?"
        (*
        mk_iff
          (mk_pred id1 argsTerm)
          (mk_pred id2 argsTerm)
        *)
      | t ->
        [mk_eq
          (mk_free_const ?srt:t id1)
          (mk_free_const ?srt:t id2)]
    in
    let v1 = snd id1 in
    let v2 = snd id2 in
      if v1 = v2 then (id1, [], [])
      else if v1 < v2 then (id2, f, [])
      else (id1, [], f)
  in
  let keys = IdMap.fold (fun t _ acc -> IdSet.add t acc) subst1 IdSet.empty in
  let keys = IdMap.fold (fun t _ acc -> IdSet.add t acc) subst2 keys in
  (*let keys = IdSet.remove (reach_id Sl.prev_pts) keys in TODO why removed ?? *)
  let signatures =
    IdMap.fold
      (fun id sign acc ->
        if IdMap.mem id acc then
          begin
            assert (sign = IdMap.find id acc);
            acc
          end
        else IdMap.add id sign acc
      )
      sig1
      sig2
  in
  let get subst id = try IdMap.find id subst with Not_found -> id in
  let get_tpe sign id =
    try IdMap.find id signatures
    with Not_found ->
      begin
        Debug.amsg ("no type for: " ^ (str_of_ident id) ^ "\n");
        None
      end
  in
    IdSet.fold
      (fun id (cs1, cs2, s, si) ->
        (* take the most recent version, if does not exists then ok. *)
        let sign = get_tpe signatures id in
        let id1 = get subst1 id in
        let id2 = get subst2 id in
        let (id3, c1, c2) = cstr_for sign id1 id2 in
          ( c1 @ cs1, c2 @ cs2,
            IdMap.add id id3 s,
            si )
      )
      keys
      ([], [], IdMap.empty, signatures)

(* Returns a subst that unifies the two branches of an if
 * i.e. if something is changed in at least one branch then
 * creates a fresh id and add some equality constraints.
 *)
let unify stack branch1 branch2 =
  Debug.msg ("unify, branch1\n" ^ (DecisionStack.subst_to_string (DecisionStack.get_subst branch1)) ^ "\n");
  Debug.msg ("unify, branch2\n" ^ (DecisionStack.subst_to_string (DecisionStack.get_subst branch2)) ^ "\n");
  (* assumes the axioms have already been guarded. *)
  let ax1 = DecisionStack.axioms branch1 in
  let ax2 = DecisionStack.axioms branch2 in
  (* conditions: c1 xor ~c2 *)
  let last lst = List.nth lst ((List.length lst) - 1) in
  let c1 = match last branch1 with
    | DecisionStack.Branch c -> c
    | _ -> failwith "expected DecisionStack.branch"
  in
  let c2 = match last branch2 with
    | DecisionStack.Branch c -> c
    | _ -> failwith "expected DecisionStack.branch"
  in
  (* steps *)
  let stp1 = DecisionStack.steps branch1 in
  let stp2 = DecisionStack.steps branch2 in
  (* substitutions *)
  let s1 = DecisionStack.get_subst branch1 in
  let s2 = DecisionStack.get_subst branch2 in
  (* signatures *)
  let sig1 = DecisionStack.get_sign branch1 in
  let sig2 = DecisionStack.get_sign branch2 in
  let (cs1, cs2, s3, sig3) = unify_subst sig1 sig2 s1 s2 in
  (* put things together *)
  let all_axioms = ax1 @ ax2 in
  let stack_with_axioms = List.fold_left DecisionStack.axiom stack all_axioms in
  let b1 = smk_and (c1 :: cs1 @ stp1) in
  let b2 = smk_and (c2 :: cs2 @ stp2) in
  let both_branches = mk_or [b1; b2] in
    DecisionStack.step stack_with_axioms both_branches s3 sig3
  
let add_to_stack stack subst sign cstr =
  let (ax, fs) = extract_axioms (Sl.get_clauses cstr) in
    List.fold_left
      DecisionStack.guard_and_add
      (DecisionStack.step stack (smk_and fs) subst sign)
      ax

let check_entailment what pre_sl stack post_sl =
  (* TODO less copy-paste with Entails *)
  Debug.msg ("checking VC: " ^ what ^ "\n");
  Debug.msg ("precondition: " ^ (Sl.to_string pre_sl) ^ "\n");
  Debug.msg ("postcondition: " ^ (Sl.to_string post_sl) ^ "\n");
  Debug.msg ("stack:\n" ^ (DecisionStack.to_string stack) ^ "\n");
  Debug.msg ("subst:\n" ^ (DecisionStack.subst_to_string (DecisionStack.get_subst stack)) ^ "\n");
  let subst = DecisionStack.get_subst stack in
  let preh = Entails.pre_heap () in
  let posth = Entails.post_heap () in
  let pre = to_grass preh pre_sl IdMap.empty in
  let pathf = DecisionStack.get_form stack in
  let post_neg = to_grass_negated posth post_sl subst in
  let heap_content = Entails.same_heap_axioms subst preh posth in
  let wo_axioms = pre :: pathf @ [post_neg] in
  let query = nnf (smk_and (heap_content @ wo_axioms)) in
  let _ = if !Debug.verbose then
    begin
      print_endline "query wo axioms: ";
      print_form stdout (smk_and (wo_axioms @ heap_content));
      print_newline ()
    end
  in
  let sat = 
    if query = mk_false then (Debug.msg "Assertion holds trivially\n"; Some false)
    else Prover.check_sat ~session_name:what query 
  in
  match sat with
  | Some true -> failwith ("cannot prove assertion (sat) for " ^ what) (*TODO model*)
  | Some false -> ()
  | None -> failwith ("cannot prove assertion (unk) for " ^ what)

let check_grass_entailment what pre_sl stack post_grass =
  (* TODO less copy-paste with Entails *)
  Debug.msg ("checking VC: " ^ what ^ "\n");
  Debug.msg ("precondition: " ^ (Sl.to_string pre_sl) ^ "\n");
  Debug.msg ("postcondition: " ^ (string_of_form post_grass) ^ "\n");
  Debug.msg ("stack:\n" ^ (DecisionStack.to_string stack) ^ "\n");
  Debug.msg ("subst:\n" ^ (DecisionStack.subst_to_string (DecisionStack.get_subst stack)) ^ "\n");
  let subst = DecisionStack.get_subst stack in
  let preh = Entails.pre_heap () in
  let posth = Entails.post_heap () in
  let pre = to_grass preh pre_sl IdMap.empty in
  let pathf = DecisionStack.get_form stack in
  let post_neg = subst_id subst (mk_not post_grass) in
  let heap_content = Entails.same_heap_axioms subst preh posth in
  let wo_axioms = pre :: pathf @ [post_neg] in
  let query = nnf (smk_and (heap_content @ wo_axioms)) in
  let _ = if !Debug.verbose then
    begin
      print_endline "query wo axioms: ";
      print_form stdout (smk_and (wo_axioms @ heap_content));
      print_newline ()
    end
  in
  let sat = 
    if query = mk_false then (Debug.msg "Assertion holds trivially\n"; Some false)
    else Prover.check_sat ~session_name:what query 
  in
  match sat with
  | Some true -> failwith ("cannot prove assertion (sat) for " ^ what) (*TODO model*)
  | Some false -> ()
  | None -> failwith ("cannot prove assertion (unk) for " ^ what)


(* Checks whether the frame exists *)
let is_frame_defined name pre_sl pathf post_sl subst =
  let preh = Entails.pre_heap () in
  let posth = Entails.post_heap () in
  let pre = to_grass preh pre_sl IdMap.empty in
  let post = to_grass_not_contained posth post_sl subst in
  let query = nnf (smk_and ( (mk_and (pre :: post :: pathf)) ::
                           (Entails.same_heap_axioms subst preh posth) ) )
  in
    match Prover.check_sat ~session_name:name query with
    | Some b -> not b
    | None -> failwith "is_frame_defined: Prover returned None"


(* checks is a frame exists (non-tight entailment) *)
let check_if_frame_exists name pre stack sl =
  Debug.msg ("checking the existence of a frame.\n");
  let subst = DecisionStack.get_subst stack in
  let pathf = DecisionStack.get_form stack in
    is_frame_defined name pre pathf sl subst

(* ... *)
let check_procedure proceduresMap name =
  print_endline ("checking: " ^ (str_of_ident name));
  let get name = 
    try IdMap.find name proceduresMap
    with Not_found -> failwith ("ERROR: method "^(str_of_ident name)^" not found.")
  in
  (*
  let fresh_local () = fresh_ident "_" in
  let subst_with_fresh_local m subst form =
    let non_args =
      IdSet.filter
        (fun id -> not (List.mem id m.args))
        (Sl.ids form)
    in
    let subst2 =
      IdSet.fold
        (fun id acc -> IdMap.add id (fresh_local ()) acc)
        non_args
        subst
    in
      Sl.subst_id subst2 form 
  in
  *)
  let get_pre name args =
    let m = get name in
    let subst =
      List.fold_left2
        (fun acc param value ->
          IdMap.add param value acc)
        IdMap.empty
        m.args
        args
    in
      Sl.subst_id subst m.precondition
  in
  let get_post name args return =
    let m = get name in
    let subst =
      List.fold_left2
        (fun acc param value ->
          IdMap.add param value acc)
        (IdMap.add (mk_ident "returned") return IdMap.empty)
        m.args
        args
    in
      Sl.subst_id subst m.postcondition
  in

  (* aliases *)
  let mk_set = Sl.mk_loc_set in
  let mk_loc_set = Sl.mk_loc_set in
  let mk_loc = Sl.mk_loc in

  let last_alloc subst = 
    if IdMap.mem alloc_id subst
    then IdMap.find alloc_id subst
    else alloc_id
  in

  (* assume pre,stack |= sl_1 * F  for some frame F
   * then we want to replace sl_1 by sl_2 (e.g. method call)
   * we need to:
   * 1) check that F exists
   * 2) push sl_1 (not tight) -> the heap predicate give the footprint of sl_1
   * 3) push sl_2 and use the footprint of sl_1 to update the predicates like alloc
   *)
  let sl_replacement msg pre stack sl_1 subst2 sig2 sl_2 =
    Debug.msg ("sl_replacement: " ^ (Sl.to_string sl_1) ^ " by " ^ (Sl.to_string sl_2) ^ "\n");
    let cmt = str_of_ident name ^ "_" ^ Str.global_replace (Str.regexp " ") "_" msg in
    if not (check_if_frame_exists cmt pre stack sl_1) then
      failwith (msg ^ " may not hold in " ^ (str_of_ident name))
    else
      begin
        (* Sl.pts + Sl.prev_pts + TODO other pointers ? *)
        let subst = DecisionStack.get_subst stack in
        let alloc1 = last_alloc subst in
        let fp = fresh_ident "footprint" in
        let fp2 = fresh_ident "footprint" in
        let sl_1f = to_grass fp sl_1 subst in
        let sl_2f = to_grass fp2 sl_2 subst2 in
        let alloc2 = last_alloc subst2 in
        let get_pts pts subst = Sl.to_field (try IdMap.find pts subst with Not_found -> pts) in
        let get_next = get_pts Sl.pts in
        let get_prev = get_pts Sl.prev_pts in
        let has_prev = IdMap.mem Sl.prev_pts subst2 in
        let frame find_ptr =
          mk_frame
            (mk_set fp) (mk_set fp2)
            (mk_set alloc1) (mk_set alloc2)
            (find_ptr subst) (find_ptr subst2)
        in
        let frames =
          (frame get_next) ::
          (if has_prev then [frame get_prev] else [])
        in
          add_to_stack stack subst2 sig2 (smk_and (sl_1f :: sl_2f :: frames))
      end
  in
  
  let increase1 (subst, sign) id t =
    let (name, version) =
      try IdMap.find id subst
      with Not_found -> id
    in
    let tpe = 
      try IdMap.find id sign
      with Not_found -> t
    in
      IdMap.add id (name, version + 1) subst,
      IdMap.add (name, version + 1) tpe sign
  in
  let increase subst sign ids_t =
    List.fold_left
      (fun acc (ids, t) ->
        List.fold_left (fun acc i -> increase1 acc i t) acc ids)
      (subst, sign)
      ids_t
  in

  let sl_stuff_to_increase pre subst sl1 sl2 =
    (* TODO other pointers *)
    let pts = if  Sl.has_prev pre ||
                  Sl.has_prev sl1 ||
                  Sl.has_prev sl2 ||
                  IdMap.mem Sl.prev_pts subst then
        [Sl.pts; Sl.prev_pts]
      else
        [Sl.pts]
    in
      [pts, Some (Fld Loc); [alloc_id], Some (Set Loc)]
  in

  let procedure_call pre stack m args id =
    let args_id =
      List.map
        (fun f -> match f with
          | Term (App ((FreeSym id), [], _)) -> id
          | Term (App (Null, [], _)) -> mk_ident "null" (*TODO !!*)
          | _ -> failwith "for the moment, the arguments of call should be constants"
        ) args
    in
    Debug.msg ("procedure_call: " ^ (str_of_ident m) ^ "(" ^ (String.concat ", " (List.map str_of_ident args_id))^ ")\n");
    let subst = DecisionStack.get_subst stack in
    let sig1 = DecisionStack.get_sign stack in
    let m_pre = get_pre m args_id in
    let m_post = get_post m args_id id in
    let (subst2, sig2) = increase subst sig1 (sl_stuff_to_increase pre subst m_pre m_post) in 
      sl_replacement ("precondition of " ^ (str_of_ident m)) pre stack m_pre subst2 sig2 m_post
  in

  let loop_that_dont_change_heap pre stack cond invariant body =
    if not (check_if_frame_exists (str_of_ident name ^ "_invariant") pre stack invariant) then
      failwith ("loop invariant of loop in " ^ str_of_ident name ^ " may not hold initially")
    else
      begin
        let subst = DecisionStack.get_subst stack in
        let sig1 = DecisionStack.get_sign stack in
        let (subst2, sig2) = increase subst sig1 (assigned body) in
        let fp = fresh_ident "footprint" in
        let sl_f = to_grass fp invariant subst2 in
        let notC = subst_id subst2 (mk_not cond) in
          add_to_stack stack subst2 sig2 (smk_and [notC; sl_f])
      end
  in

  let while_pre_post pre stack cond invariant body =
    if (change_heap body) then
      begin
        (* pre/post *)
        let subst = DecisionStack.get_subst stack in
        let sig1 = DecisionStack.get_sign stack in
        let assigned = assigned body in
        let subst2, sig2 = increase subst sig1 (assigned @ (sl_stuff_to_increase pre subst invariant invariant)) in
        let stack2 = sl_replacement "invariant" pre stack invariant subst2 sig2 invariant in
        let notC = subst_id subst2 (mk_not cond) in
          add_to_stack stack2 subst2 sig2 notC
      end
    else
      loop_that_dont_change_heap pre stack cond invariant body
  in
  
  let proc = get name in

  let subst_ident id ident_map =
    try IdMap.find id ident_map
    with Not_found -> id
  in
  let fresh_ident id ident_map sig_map default_type =
    let name, m = subst_ident id ident_map in
    let new_id = (name, m + 1) in
    let new_ident_map = IdMap.add id new_id ident_map in
    let tpe = try IdMap.find id sig_map with Not_found -> default_type in
    let new_sig_map = IdMap.add id tpe (IdMap.add new_id tpe sig_map) in
      new_id, new_ident_map, new_sig_map
  in

  let proc_name = str_of_ident proc.name in

  let rec check pre stmnt =
    let rec traverse stack stmnt = match stmnt with
      | FunUpdate (id0, ind, Term upd) ->
        let ident_map = DecisionStack.get_subst stack in
        let sig_map = DecisionStack.get_sign stack in
        let upd1 = subst_id_term ident_map upd in
        let ind1 = subst_id_term ident_map ind in
        let id = subst_ident id0 ident_map in
        let id1, ident_map1, sig_map1 = fresh_ident id0 ident_map sig_map None in
        let tpe = IdMap.find id1 sig_map1 in
        let f =
          mk_eq
            (mk_free_const ?srt:tpe id1)
            (mk_write (mk_free_const ?srt:tpe id) ind1 upd1)
        in
          add_to_stack stack ident_map1 sig_map1 f
      | VarUpdate (id, Term t) ->
        let ident_map = DecisionStack.get_subst stack in
        let sig_map = DecisionStack.get_sign stack in
        let t1 = subst_id_term ident_map t in
        let id1, ident_map1, sig_map1 = fresh_ident id ident_map sig_map None in
        let f = mk_eq (mk_free_const id1) t1 in
          add_to_stack stack ident_map1 sig_map1 f
      | Dispose id ->
        let ident_map = DecisionStack.get_subst stack in
        let sig_map = DecisionStack.get_sign stack in
        let id1 = (subst_ident id ident_map) in
        let alloc = subst_ident alloc_id ident_map in
        let alloc1, ident_map1, sig_map1 = fresh_ident alloc_id ident_map sig_map (Some (Set Loc)) in
        let f =
          mk_eq
            (mk_loc_set alloc1)
            (mk_diff (mk_loc_set alloc) (mk_setenum [mk_loc id1]))
        in
          add_to_stack stack ident_map1 sig_map1 f
      | New id ->
        let ident_map = DecisionStack.get_subst stack in
        let sig_map = DecisionStack.get_sign stack in
        let id1, ident_map1, sig_map1 = fresh_ident id ident_map sig_map (Some Loc) in
        let alloc = subst_ident alloc_id ident_map1 in
        let alloc1, ident_map2, sig_map2 = fresh_ident alloc_id ident_map1 sig_map1 (Some (Set Loc)) in
        let f =
          mk_and [
            mk_eq
              (mk_loc_set alloc1)
              (mk_union [mk_loc_set alloc; mk_setenum [mk_loc id1]]);
            mk_not (mk_elem (mk_loc id1) (mk_loc_set alloc))
          ]
        in
        (* add a skolem cst v |-> _, TODO is it really needed ? *)
        let curr_pts = Sl.to_field (try IdMap.find Sl.pts ident_map2 with Not_found -> Sl.pts) in
        let skolem_pts = mk_eq (mk_read curr_pts (mk_loc id1)) (mk_loc (FormUtil.fresh_ident "default_successor")) in
        let not_null = mk_not (mk_eq mk_null (mk_loc id1)) in
        let c = smk_and [not_null; skolem_pts; f] in
          add_to_stack stack ident_map2 sig_map2 c
      | Return t -> 
        let subst = DecisionStack.get_subst stack in
        let newT = 
          match t with 
          | App (FreeSym t1, [], _) -> 
              (try IdMap.find t1 subst with Not_found -> t1)
          | App (Null, [], _) -> mk_ident "null"
          | _ -> failwith "TODO: return expects an id for the moment"
        in
        let post = proc.postcondition in
        let sign = DecisionStack.get_sign stack in
        let subst = IdMap.add (mk_ident "returned") newT subst in
        let stackWithReturn = DecisionStack.step stack mk_true subst sign in
          (*check postcond and assume false !*)
          check_entailment (proc_name ^ "_postcondition_return_" ^ (str_of_ident newT)) pre stackWithReturn post;
          DecisionStack.step stack (mk_false) IdMap.empty IdMap.empty
      | Assume f ->
        (*sll to grass*)
        let subst = DecisionStack.get_subst stack in
        let sig_map = DecisionStack.get_sign stack in
        let cur_alloc = latest_alloc subst in
        let c = to_grass cur_alloc f subst in
          add_to_stack stack subst sig_map c
      | Assert (f, cmt_opt) ->
          let cmt = match cmt_opt with
          | Some cmt -> cmt
          | None -> "assert"
          in
          check_entailment (proc_name ^ "_" ^ cmt) pre stack f;
          stack
      | AssertGrass (f, cmt_opt) ->
          let cmt = match cmt_opt with
          | Some cmt -> cmt
          | None -> "assert"
          in
          check_grass_entailment (proc_name ^ "_" ^ cmt) pre stack f;
          stack
      | AssumeGrass f ->
        let subst = DecisionStack.get_subst stack in
        let sig_map = DecisionStack.get_sign stack in
        let f2 = subst_id subst f in
          add_to_stack stack subst sig_map f2
      | Ite (cond, caseTrue, caseFalse) ->
        let subst = DecisionStack.get_subst stack in
        let c = subst_id subst cond in
        let mk_branch cond stmnt =
          let s1 = DecisionStack.push stack cond in
          let s2 = traverse s1 stmnt in
          let (branch, _) = DecisionStack.pop s2 in
            if DecisionStack.steps branch = [] (* if empty replace by assume true so we have the subst and signature *)
            then add_to_stack branch subst (DecisionStack.get_sign stack) mk_true
            else branch
        in
        let sT = mk_branch c caseTrue in
        let sF = mk_branch (mk_not c) caseFalse in
          unify stack sT sF
      | Block stmnts -> 
        List.fold_left traverse stack stmnts
      | While (cond, invariant, body) ->
        (* check the loop body *)
        Debug.msg ("checking loop body.\n");
          let _ = check invariant (Block [AssumeGrass cond; body; Assert (invariant, Some "invariant_inductive"); AssumeGrass (mk_false)]) in
          Debug.msg ("loop: pre, post, and frame.\n");
          while_pre_post pre stack cond invariant body
      | VarUpdate (id, Call (m, args)) -> 
        procedure_call pre stack m args id
        (* goal: (post[returned \mapsto id'] @ frame, subst2) *)
      | FunUpdate (id, ptr, Call (m, args)) -> 
        let ret_id = FormUtil.fresh_ident "_returned" in
        let stack2 = procedure_call pre stack m args ret_id in
        let t2 = VarUpdate (id, Term (mk_free_const ret_id)) in
          traverse stack2 t2
    in
    (* check the body *)
    let to_map lst =
      List.fold_left
        (fun acc (k,v) -> IdMap.add k v acc)
        IdMap.empty
        lst
    in
    let init_stack =
      DecisionStack.step
        DecisionStack.empty
        (smk_and (alloc_axioms ()))
        IdMap.empty
        (to_map [(alloc_id, Some (Set Loc));(Sl.pts, Some (Fld Loc));(Sl.prev_pts, Some (Fld Loc));(Sl.data, Some (Fld Int))])
    in
    let final_stack = traverse init_stack stmnt in
    (* check for postcondition (void methods) *)
    let post = proc.postcondition in
      check_entailment (proc_name ^ "_postcondition") pre final_stack post
  in
  check proc.precondition (desugar proc.body)

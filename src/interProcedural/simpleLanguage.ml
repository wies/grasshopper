open Form
open Axioms

type expr =
  | Term of term
  | Call of ident * expr list

type stmnt =
  | VarUpdate of ident * expr 
  | FunUpdate of ident * term * expr
  | New of ident
  | Dispose of ident
  | Assume of Sl.form
  | Assume2 of form
  | Assert of Sl.form
  | Block of stmnt list
  | While of form * Sl.form * stmnt
  | Ite of form * stmnt * stmnt
  | Return of term

type procedure = {
  name: ident;
  args: ident list;
  precondition: Sl.form;
  postcondition: Sl.form;
  body: stmnt
}

let rec assigned stmnt = match stmnt with
  | Assume _ | Assume2 _ | Assert _ | Return _ -> IdSet.empty
  | VarUpdate (t, _) | FunUpdate (t, _, _) | New t -> IdSet.singleton t
  | Dispose _ -> IdSet.empty
  | Block lst -> List.fold_left (fun acc s -> IdSet.union acc (assigned s)) IdSet.empty lst
  | While (_, _, s) -> assigned s
  | Ite (_, s1, s2) -> IdSet.union (assigned s1) (assigned s2)

module DecisionStack =
  struct

    type subst = ident IdMap.t

    let subst_to_string subst =
      String.concat "\n"
        (List.map
          (fun (id1, id2) ->
            (str_of_ident id1) ^ " -> " ^ (str_of_ident id2)
          )
          (IdMap.bindings subst) )

    type kind = Step of form * subst
              | Branch of form
              | Axiom of form
              (*TODO a cut thing (drop everything before?? for calls, loops, ...) *)

    let is_step k = match k with
      | Step _ -> true
      | _ -> false
    let is_branch k = match k with
      | Branch _ -> true
      | _ -> false
    let is_axiom k = match k with
      | Axiom _ -> true
      | _ -> false

    let kind_to_string k = match k with
      | Step (f, _) -> "Step: " ^ (string_of_form f)
      | Branch f -> "Branch: " ^ (string_of_form f)
      | Axiom f -> "Axiom: " ^ (string_of_form f)

    type t = kind list

    let empty = []

    let to_string stack =
      String.concat "\n" (List.map kind_to_string stack)

    let step stack f s = (Step (f, s)) :: stack

    let axiom stack f = (Axiom f) :: stack

    let push stack f = (Branch f) :: stack

    (** Returns (a, b) where a is the part that was poped, b is the new stack.*)
    let pop stack =
      let rec pop1 acc stack = match stack with
        | ((Step _) as x) :: xs -> pop1 (x :: acc) xs
        | ((Axiom _) as x):: xs -> pop1 (x :: acc) xs
        | ((Branch _) as x) :: xs -> ((List.rev (x :: acc)), xs)
        | [] -> failwith "popping an empty stack."
      in
        pop1 [] stack

    let fold_topdown = List.fold_left
    let fold_bottomup = List.fold_right
    let map = List.map
    let filter = List.filter

    let get_form stack =
      let get k = match k with
        | Step (f, _) -> f
        | Branch f -> f
        | Axiom f -> f
      in
        map get stack

    let conditions stack =
        get_form (filter is_branch stack)
    
    let axioms stack =
        get_form (filter is_axiom stack)
    
    let steps stack =
        get_form (filter is_step stack)

    let get_subst stack =
      try 
        match List.find is_step stack with
        | Step (m, s) -> s
        | _ -> failwith "is_step ?!?"
      with Not_found -> IdMap.empty

    (** makes an axiom depends on the currents decisions *)
    let guard_axiom stack f =
      mk_implies (mk_and (conditions stack)) f

    let guard_and_add stack f =
        axiom stack (guard_axiom stack f)

    let ground_terms stack =
      List.fold_left
        (fun acc f -> TermSet.union (ground_terms f) acc)
        TermSet.empty
        (get_form stack)

  end
      
let to_stmnt s = match s with
  | VarUpdate (id, Term t) -> Stmnt.VarUpdate (id, t)
  | FunUpdate (id, ptr, Term t) -> Stmnt.FunUpdate (id, ptr, t)
  | New id -> Stmnt.New id
  | Dispose id -> Stmnt.Dispose id
  | _ -> failwith("cannot convert")

let convert stmnt subst =
  let (cstr, subst) = Stmnt.ssa_partial subst [(to_stmnt stmnt)] in
    (Form.smk_and (List.flatten cstr), subst)

let latest_alloc subst =
  if IdMap.mem alloc_id subst
  then IdMap.find alloc_id subst
  else alloc_id

let to_lolli heap sl =
  Sl.to_lolli heap sl

let to_lolli_negated heap sl =
  Sl.to_lolli_negated heap sl

let rec get_clauses f = match f with
  | And lst -> List.flatten (List.map get_clauses lst)
  | Comment (c, f) -> List.map (fun x -> Comment (c,x)) (get_clauses f)
  | other -> [other]


let unify_subst subst1 subst2 =
  let cstr_for id1 id2 =
    let mk_axioms args =
      mk_equiv
        (mk_pred id1 args)
        (mk_pred id2 args)
    in
    let (ax, cstr) =
      (* is a predicate or a cst ? *)
      if Axioms.is_reach id1 then
        ([mk_axioms [var1; var2; var3]], [])
      else if Axioms.is_jp id1 then
        ([mk_axioms [var1; var2]], [])
      else if fst id1 = fst Axioms.alloc_id then
        ([mk_axioms [var1]], [])
      else (* constants *)
        ([], [mk_eq (mk_const id1) (mk_const id2)])
    in
    let v1 = snd id1 in
    let v2 = snd id2 in
      if v1 = v2 then (id1, [], [], [], [])
      else if v1 < v2 then (id2, ax, cstr, [], [])
      else (id1, [], [], ax, cstr)
  in
  let keys1 = IdMap.fold (fun t _ acc -> IdSet.add t acc) subst1 IdSet.empty in
  let keys  = IdMap.fold (fun t _ acc -> IdSet.add t acc) subst2 keys1 in
    IdSet.fold
      (fun id (as1, cs1, as2, cs2, s) ->
        (* take the most recent version, if does not exists then ok. *)
        let (id3, a1, c1, a2, c2) = match (IdMap.mem id subst1, IdMap.mem id subst2) with
          | (true, true) ->
            let id1 = IdMap.find id subst1 in
            let id2 = IdMap.find id subst2 in
              cstr_for id1 id2
          | (true, false) ->
            (id, [], [], [], [])
          | (false, true) ->
            (id, [], [], [], [])
          | (false, false) ->
            failwith "not possible"
        in
          ( a1 @ as1, c1 @ cs1,
            a2 @ as2, c2 @ cs2,
            IdMap.add id id3 s )
      )
      keys
      ([], [], [], [], IdMap.empty)

(* Returns a subst that unifies the two branches of an if
 * i.e. if something is changed in at least one branch then
 * creates a fresh id and add some equality constraints.
 *)
let unify stack branch1 branch2 =
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
  let (as1, cs1, as2, cs2, s3) = unify_subst s1 s2 in
  (* put things together *)
  let all_axioms =
    (List.map (fun a -> mk_implies c1 a) as1) @
    (List.map (fun a -> mk_implies c2 a) as2) @
    ax1 @ ax2
  in
  let stack_with_axioms = List.fold_left DecisionStack.axiom stack all_axioms in
  let b1 = smk_and (c1 :: cs1 @ stp1) in
  let b2 = smk_and (c2 :: cs2 @ stp2) in
  let both_branches = mk_or [b1; b2] in
    DecisionStack.step stack_with_axioms both_branches s3
  
let add_to_stack stack subst cstr =
  let (ax, fs) = Axioms.extract_axioms (get_clauses cstr) in
    List.fold_left
      DecisionStack.guard_and_add
      (DecisionStack.step stack (smk_and fs) subst)
      ax

let check_entailment what pre_sl stack post_sl =
  (* TODO less copy-paste with Entails *)
  Debug.msg ("checking entailment: " ^ what ^ "\n");
  Debug.msg ("checking entailment: precondition " ^ (Sl.to_string pre_sl) ^ "\n");
  Debug.msg ("checking entailment: postcondition " ^ (Sl.to_string post_sl) ^ "\n");
  Debug.msg ("checking entailment: stack\n" ^ (DecisionStack.to_string stack) ^ "\n");
  Debug.msg ("checking entailment: subst\n" ^ (DecisionStack.subst_to_string (DecisionStack.get_subst stack)) ^ "\n");
  let subst = DecisionStack.get_subst stack in
  let pre = to_lolli Entails.pre_heap pre_sl in
  let pathf = DecisionStack.get_form stack in
  let post_neg = subst_id subst (to_lolli_negated Entails.post_heap post_sl) in
  let heap_content = Entails.same_heap_axioms subst in
  let wo_axioms = pre :: pathf @ [post_neg] in
  let axioms = List.flatten (Axioms.make_axioms [wo_axioms]) in
  let query = smk_and (axioms @ heap_content @ wo_axioms) in
  let _ = if !Debug.verbose then
    begin
      print_endline "query wo axioms: ";
      print_form stdout (mk_and (wo_axioms @ heap_content))(*;
      print_endline "query: ";
      print_form stdout query*)
    end
  in
  let sat = Prover.satisfiable query in
    match sat with
    | Some true -> failwith ("cannot prove assertion (sat) for " ^ what) (*TODO model*)
    | Some false -> ()
    | None -> failwith ("cannot prove assertion (unk) for " ^ what)

(* checks is a frame exists (non-tight entailment) *)
let check_if_frame_exists pre stack sl =
  let subst = DecisionStack.get_subst stack in
  let pathf = DecisionStack.get_form stack in
    Frame.is_frame_defined pre pathf sl subst

let compute_frames pre_sl stack post_sl =
  Debug.msg ("compute frames: precondition " ^ (Sl.to_string pre_sl) ^ "\n");
  Debug.msg ("compute frames: postcondition " ^ (Sl.to_string post_sl) ^ "\n");
  Debug.msg ("compute frames: stack\n" ^ (DecisionStack.to_string stack) ^ "\n");
  Debug.msg ("compute frames: subst\n" ^ (DecisionStack.subst_to_string (DecisionStack.get_subst stack)) ^ "\n");
  let subst = DecisionStack.get_subst stack in
  let pre = to_lolli Entails.pre_heap pre_sl in
  let path = DecisionStack.get_form stack in
  let post = subst_id subst (to_lolli Entails.post_heap post_sl) in
  let query = Frame.mk_frame_query pre path post subst in
  let frames = Frame.infer_frame_loop subst query in
    frames

(* ... *)
let check_procedure proceduresMap name =
  print_endline ("checking: " ^ (str_of_ident name));
  let get name = IdMap.find name proceduresMap in
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
      subst_with_fresh_local m subst m.precondition
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
      subst_with_fresh_local m subst m.postcondition
  in

  let replacement_alloc alloc1 fp1 alloc2 fp2 =
    let mk_pred d = Form.mk_pred d [Axioms.var1] in
    let a1 = mk_pred alloc1 in
    let a2 = mk_pred alloc2 in
    let f1 = mk_pred fp1 in
    let f2 = mk_pred fp2 in
    let nf1a1 = Form.mk_and [Form.mk_not f1; a1] in
      Sl.mk_forall
        (Form.mk_and [
          (*Form.mk_implies (mk_pred fp1) (mk_pred alloc1);*)
          Form.mk_implies f2 a2;
          Form.mk_implies nf1a1 a2;
          Form.mk_implies a2 (Form.mk_or [f2; nf1a1])
        ])
          (*
          Form.mk_implies (Form.mk_and [Form.mk_not (mk_pred fp1); Form.mk_not (mk_pred fp2)]) (Form.mk_equiv (mk_pred alloc2) (mk_pred alloc1))
          Form.mk_and [mk_pred fp1; Form.mk_equiv (mk_pred alloc2) (mk_pred fp2)]
          Form.mk_and [Form.mk_not (mk_pred fp1); Form.mk_equiv (mk_pred alloc2) (mk_pred alloc1)]
          *)
  in

  let replacement_pts fp1 pts1 pts2 =
    let mk_pred d = Form.mk_pred d [Axioms.var1] in
    let mk_app d = Form.mk_app d [Axioms.var1] in
      Sl.mk_forall
        (Form.mk_implies
          (Form.mk_not (mk_pred fp1))
          (Form.mk_eq (mk_app pts1) (mk_app pts2))
        )
  in

  let replacement_reach fp1 r1 r2 =
    let mk_pred d = Form.mk_pred d [Axioms.var1] in
    let ep v = Axioms.ep fp1 v in
    let reach1 x y z = Form.mk_pred r1 [x; y; z] in
    let reach2 x y z = Form.mk_pred r2 [x; y; z] in
      (Sl.mk_forall
        (Form.mk_implies
          (Form.mk_and 
	     [Form.mk_not (mk_pred fp1); 
	      reach1 Axioms.var1 Axioms.var2 (ep Axioms.var1)])
          (Form.mk_equiv 
	     (reach1 Axioms.var1 Axioms.var2 var3)
             (reach2 Axioms.var1 Axioms.var2 var3))
        )
      )(* :: (Sl.mk_forall
        (Form.mk_implies
          (Form.mk_not (mk_pred fp1))
          (Form.mk_equiv (reach1 Axioms.var1 (ep Axioms.var1) Axioms.var2)
                         (reach2 Axioms.var1 (ep Axioms.var1) Axioms.var2))
        )
      )*) :: (Sl.mk_forall
        (Form.mk_implies
          (Form.mk_and [Form.mk_not (mk_pred fp1); Form.mk_eq Axioms.var1 (ep Axioms.var1)])
          (Form.mk_equiv (reach1 Axioms.var1 Axioms.var2 Axioms.var3)
                         (reach2 Axioms.var1 Axioms.var2 Axioms.var3))
        )
      ) :: (Axioms.ep_axioms fp1 (Axioms.fun_of_reach r1))
  in

  (* assume pre,stack |= sl_1 * F  for some frame F
   * then we want to replace sl_1 by sl_2 (e.g. method call)
   * we need to:
   * 1) check that F exists
   * 2) push sl_1 (not tight) -> the heap predicate give the footprint of sl_1
   * 3) push sl_2 and use the footprint of sl_1 to update the predicates like alloc
   *)
  let sl_replacement pre stack sl_1 subst2 sl_2 =
    Debug.msg ("sl_replacement: " ^ (Sl.to_string sl_1) ^ " by " ^ (Sl.to_string sl_2) ^ "\n");
    if not (check_if_frame_exists pre stack sl_1) then
      failwith "sl_replacement: precondition is not respected"
    else
      begin
        let subst = DecisionStack.get_subst stack in
        let alloc1 = Frame.last_alloc subst in
        let fp = fresh_ident "footprint" in
        let fp2 = fresh_ident "footprint" in
        let sl_1f = Form.subst_id subst (Sl.to_lolli fp sl_1) in
        let included = Sl.mk_forall (Sl.set_included fp alloc1) in
	let preserve = Sl.mk_forall 
	    (Form.mk_implies (mk_and [Sl.set_in alloc1 Axioms.var1; Sl.set_in fp2 Axioms.var1])
	    (Sl.set_in fp Axioms.var1)) 
	in
        let sl_2f = Form.subst_id subst2 (Sl.to_lolli fp2 sl_2) in
        (*let included2 = Sl.mk_forall (Sl.set_included fp2 alloc2) in*)
        let alloc2 = Frame.last_alloc subst2 in
        let get_pts subst = try IdMap.find Sl.pts subst with Not_found -> Sl.pts in
        let get_reach subst = try IdMap.find (Axioms.reach_id Sl.pts) subst with Not_found -> (Axioms.reach_id Sl.pts) in
        let axioms =
          (replacement_alloc alloc1 fp alloc2 fp2) ::
          (replacement_pts fp (get_pts subst) (get_pts subst2)) ::
          (replacement_reach fp (get_reach subst) (get_reach subst2))
        in
        (*
        let ground_terms =
          List.fold_left TermSet.union TermSet.empty [
              DecisionStack.ground_terms stack;
              ground_terms (Sl.to_lolli Entails.pre_heap pre);
              ground_terms sl_1f;
              ground_terms sl_2f
            ]
        in
        let trivial_ep v = Form.mk_eq (Axioms.ep fp v) (Axioms.ep fp v) in
        let inject_ep =
          Form.mk_and (TermSet.fold (fun t acc -> (trivial_ep t):: acc) ground_terms [])
        in
        *)
          add_to_stack stack subst2 (Form.smk_and ((*inject_ep ::*) sl_1f :: included :: preserve :: sl_2f :: axioms))
      end
  in
  
  let increase1 subst id =
    let (name, version) =
      try IdMap.find id subst
      with Not_found -> id
    in
      IdMap.add id (name, version + 1) subst
  in
  let increase subst ids =
    List.fold_left increase1 subst ids
  in

  let procedure_call pre stack m args id =
    let args_id =
      List.map
        (fun f -> match f with
          | Term (Form.Const id) -> id
          | _ -> failwith "for the moment, the arguments of call should be constants"
        ) args
    in
    Debug.msg ("procedure_call: " ^ (str_of_ident m) ^ "(" ^ (String.concat ", " (List.map str_of_ident args_id))^ ")\n");
    let subst = DecisionStack.get_subst stack in
    let subst2 = increase subst [Sl.pts; Axioms.reach_id Sl.pts; Axioms.alloc_id; id] in 
    let m_pre = get_pre m args_id in
    let m_post = get_post m args_id id in
      sl_replacement pre stack m_pre subst2 m_post
  in

  let while_pre_post pre stack cond invariant body =
    (* pre/post *)
    let subst = DecisionStack.get_subst stack in
    let assigned = IdSet.elements (assigned body) in
    let subst2 = increase subst (Sl.pts :: (Axioms.reach_id Sl.pts) :: Axioms.alloc_id :: assigned) in
    let stack2 = sl_replacement pre stack invariant subst2 invariant in
    let notC = subst_id subst2 (Form.Not cond) in
      add_to_stack stack2 subst2 notC
  in
  
  let proc = get name in

  let rec check pre stmnt =
    let rec traverse stack stmnt = match stmnt with
      | VarUpdate (_, Term _) | FunUpdate (_, _, Term _) | Dispose _ ->
        let (c, s) = convert stmnt (DecisionStack.get_subst stack) in
          add_to_stack stack s c
      | New v ->
        let (c, s) = convert stmnt (DecisionStack.get_subst stack) in
        (* add a skolem cst v |-> _ *)
        let v2 = IdMap.find v s in
        let skolem_pts = Form.mk_eq (Form.mk_app Sl.pts [Form.mk_const v2]) (Form.mk_const (fresh_ident "_")) in
        let not_null = Form.mk_not (Form.mk_eq Axioms.null (Form.mk_const v2)) in
        let c = Form.smk_and [not_null; skolem_pts; c] in
          add_to_stack stack s c
      | Return (Form.Const t) -> 
        let post = proc.postcondition in
        let subst = DecisionStack.get_subst stack in
        let newT = try IdMap.find t subst with Not_found -> t in
        let subst = IdMap.add (mk_ident "returned") newT subst in
        let stackWithReturn = DecisionStack.step stack (Form.BoolConst true) subst in
          (*check postcond and assume false !*)
          check_entailment ("return " ^ (str_of_ident newT)) pre stackWithReturn post;
          DecisionStack.step stack (Form.BoolConst false) IdMap.empty
      | Return t -> failwith "TODO: return expect an id for the moment"
      | Assume f ->
        (*sll to lolli*)
        let subst = DecisionStack.get_subst stack in
        let cur_alloc = latest_alloc subst in
        let c = subst_id subst (to_lolli cur_alloc f) in
          add_to_stack stack subst c
      | Assert f ->
        check_entailment ("assertion " ^ (Sl.to_string f)) pre stack f;
        stack
      | Assume2 f ->
        let subst = DecisionStack.get_subst stack in
        let f2 = subst_id subst f in
          add_to_stack stack subst f2
      | Ite (cond, caseTrue, caseFalse) ->
        let subst = DecisionStack.get_subst stack in
        let c = subst_id subst cond in
        let mk_branch cond stmnt =
          let s1 = DecisionStack.push stack cond in
          let s2 = traverse s1 stmnt in
          let (branch, _) = DecisionStack.pop s2 in
            branch
        in
        let sT = mk_branch c caseTrue in
        let sF = mk_branch (Not c) caseFalse in
          unify stack sT sF
      | Block stmnts -> 
        List.fold_left traverse stack stmnts
      | While (cond, invariant, body) ->
        (* check the loop body *)
        let _ = check invariant (Block [Assume2 cond; body; Assert invariant; Assume2 (BoolConst false)]) in
          while_pre_post pre stack cond invariant body
      | VarUpdate (id, Call (m, args)) -> 
        procedure_call pre stack m args id
        (* goal: (post[returned \mapsto id'] @ frame, subst2) *)
      | FunUpdate (id, ptr, Call (m, args)) -> 
        let ret_id = fresh_ident "_returned" in
        let stack2 = procedure_call pre stack m args ret_id in
        let t2 = VarUpdate (id, Term (Form.Const ret_id)) in
          traverse stack2 t2
    in
    (* check the body *)
    let final_stack = traverse DecisionStack.empty stmnt in
    (* check for postcondition (void methods) *)
    let post = proc.postcondition in
      check_entailment "endOfMethod" pre final_stack post
  in
    check proc.precondition proc.body

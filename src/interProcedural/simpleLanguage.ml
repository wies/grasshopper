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

(* TODO a proof object to link the different parts and the FI.
   pre: formula + option frame ID
   post: formula + option frame ID
   path: assume(pre), statment list, assert(post)
   call: (1) substitute the args in pre, need FI.
         (2) substitute the args in post, add frame from (1)
   while: (1) assert invariant + FI
          (2) assume condition + invariant, loop body, assert invariant
          (3) assume ~condition + invariant, add frame, continue ...
   ite: -> case splitting to the solver
*)
  
(* for pre and post conditions, do we need special variables:
   old(v) + return for the postcond
   old(v) is refering to the value at the moment of the call
   return is a special var (used in subst after the call)
*)

(* problem: seq needs intermediate annotation, here we don't have those ...
   can we replace them with place holder ?
   how to get both at the same time the constraints for correctness and for the frame inference ?
   exploring the proof tree (inorder) should give the path needed for the frame inference 
type proof = 
  | Seq of (*path*) proof list
  | DischargedElsewhere of stmnt
  | Branch of stmnt * (*true*) proof option * (*false*) proof option
  | Loop of stmnt * (*frame*) Sl.sl_form * (*inside*) proof
  | CallSite of stmnt * (*frame*) Sl.sl_form
  | Assertion of stmnt
  
type m_proof = procedure * (*pre*) Sl.sl_form * proof * (*post*) Sl.sl_form
*)

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
  Sl.to_lolli heap (Sl.mk_not sl)

let rec get_clauses f = match f with
  | And lst -> List.flatten (List.map get_clauses lst)
  | Comment (c, f) -> List.map (fun x -> Comment (c,x)) (get_clauses f)
  | other -> [other]

let refresh subst_map =
  IdMap.map (fun id -> (fst id, (snd id) + 1)) subst_map

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
  (*TODO something is not right*)
  let post_neg = subst_id subst (to_lolli_negated Entails.post_heap post_sl) in
  let heap_content = Entails.same_heap_axioms subst in
  let axioms = List.flatten (Axioms.make_axioms [pre :: pathf @ [post_neg]]) in
  let query = smk_and (axioms @ heap_content @ [pre] @ pathf @ [post_neg]) in
  let _ = if !Debug.verbose then
    begin
      print_endline "query: ";
      print_form stdout query
    end
  in
  let sat = Prover.satisfiable query in
    match sat with
    | Some true -> failwith ("cannot prove assertion (sat) for " ^ what) (*TODO model*)
    | Some false -> ()
    | None -> failwith ("cannot prove assertion (unk) for " ^ what)

let compute_frames pre_sl stack post_sl =
  Debug.msg ("compute frames: precondition " ^ (Sl.to_string pre_sl) ^ "\n");
  Debug.msg ("compute frames: postcondition " ^ (Sl.to_string post_sl) ^ "\n");
  Debug.msg ("compute frames: stack\n" ^ (DecisionStack.to_string stack) ^ "\n");
  Debug.msg ("compute frames: subst\n" ^ (DecisionStack.subst_to_string (DecisionStack.get_subst stack)) ^ "\n");
  let subst = DecisionStack.get_subst stack in
  let pre = to_lolli Entails.pre_heap pre_sl in
  let path = DecisionStack.get_form stack in
  let post = subst_id subst (to_lolli Entails.post_heap post_sl) in
  let query = FrameInference.mk_frame_query pre path post subst in
  let frames = FrameInference.infer_frame_loop subst query in
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
    
  let procedure_call pre stack m args id =
    let args_id =
      List.map
        (fun f -> match f with
          | Term (Form.Const id) -> id
          | _ -> failwith "for the moment, the arguments of call should be constants"
        ) args
    in
    Debug.msg ("procedure_call: " ^ (str_of_ident m) ^ "(" ^ (String.concat ", " (List.map str_of_ident args_id))^ ")\n");
    let m_pre = get_pre m args_id in
    let opt_frames = compute_frames pre stack m_pre in
    let frames = match opt_frames with
      | Some(lst) ->
        List.map
          (Sl.map_id (fun id -> if (fst id) = "_" then id else (fst id, 0))) (* reset non wildcard idents *)
          lst
      | None -> failwith "method call: precondition not satisfied"
    in
    let m_post = get_post m args_id id in
    let formula = FrameInference.combine_frames_with_f m_post frames in
    Debug.msg ("procedure call: postcondition is " ^ (Sl.to_string formula) ^ "\n");
    let subst = DecisionStack.get_subst stack in
    let subst2 = refresh subst in
    let heap = latest_alloc subst2 in
    let f1 = to_lolli heap formula in
    let f2 = subst_id subst2 f1 in
    (*
    Debug.msg ("procedure_call: subst\n" ^ (DecisionStack.subst_to_string subst) ^ "\n");
    Debug.msg ("procedure_call: subst2\n" ^ (DecisionStack.subst_to_string subst2) ^ "\n");
    Debug.msg ("procedure_call: f1\n" ^ (string_of_form f1) ^ "\n");
    Debug.msg ("procedure_call: f2\n" ^ (string_of_form f2) ^ "\n");
    *)
      (f2, subst2)
  in
  
  let proc = get name in

  let rec check pre stmnt =
    let rec traverse stack stmnt = match stmnt with
      | VarUpdate (_, Term _) | FunUpdate (_, _, Term _)
      | New _ | Dispose _ ->
        let (c, s) = convert stmnt (DecisionStack.get_subst stack) in
          add_to_stack stack s c
      | Return (Form.Const t) -> 
        let post = proc.postcondition in
        let subst = DecisionStack.get_subst stack in
        let newT = try IdMap.find t subst with Not_found -> t in
        let subst = IdMap.add (mk_ident "returned") newT subst in
        let stackWithReturn = DecisionStack.step stack (Form.BoolConst true) subst in
          (*check postcond and assume false !*)
          check_entailment "return" pre stackWithReturn post;
          DecisionStack.step stack (Form.BoolConst false) IdMap.empty
      | Return t -> failwith "TODO: return expect an id for the moment"
      | Assume f ->
        (*sll to lolli*)
        let subst = DecisionStack.get_subst stack in
        let cur_alloc = latest_alloc subst in
        let c = subst_id subst (to_lolli cur_alloc f) in
          add_to_stack stack subst c
      | Assert f ->
        check_entailment "assertion" pre stack f;
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
        let _ = check invariant (Block [Assume2 cond; body; Assert invariant]) in
        (* state after the loop:
         * -compute the frame
         * -get fresh ids
         * -goal: (Not cond) /\ (invariant * frame) *)
        let opt_frames = compute_frames pre stack invariant in
        let frames = match opt_frames with
          | Some(lst) -> List.map Sl.reset_ident lst 
          | None -> failwith "while loop: invariant not satisfied when entering the loop"
        in
        let formula = FrameInference.combine_frames_with_f invariant frames in
        let subst = DecisionStack.get_subst stack in
        let subst2 = refresh subst in
        let notC = subst_id subst2 (Form.Not cond) in
        let heap = latest_alloc subst2 in
        let f2 = subst_id subst2 (to_lolli heap formula) in
          add_to_stack stack subst2 (smk_and [notC; f2])
        
      | VarUpdate (id, Call (m, args)) -> 
        let f2, subst2 = procedure_call pre stack m args id in
          add_to_stack stack subst2 f2
        (* goal: (post[returned \mapsto id'] @ frame, subst2) *)
      | FunUpdate (id, ptr, Call (m, args)) -> 
        let ret_id = fresh_ident "_returned" in
        let f2, subst2 = procedure_call pre stack m args ret_id in
        let stack2 = add_to_stack stack subst2 f2 in
        let t2 = VarUpdate (id, Term (Form.Const ret_id)) in
          traverse stack2 t2
    in
    (* check the body *)
    let final_stack = traverse DecisionStack.empty stmnt in
    (* check for postcondition (void methods) *)
    let post = proc.postcondition in
      check_entailment "endOfMethod" pre final_stack post;
  in
    check proc.precondition proc.body

open Form
open Axioms
open Stmnt
open Entails

module IdMap = Form.IdMap
module IdSet = Form.IdSet

let last_alloc subst = 
  if IdMap.mem alloc_id subst
  then IdMap.find alloc_id subst
  else alloc_id

let implies_heap_content subst =
  (* heap axiom: B(x) => A(x)
   * if we have a path then we must compare
   * A(x) with first_alloc(x) and
   * B(x) with last_alloc(x)
   *)
  let first_alloc = alloc_id in
  let last_alloc = last_alloc subst in
  let a_x = mk_pred pre_heap [var1] in
  let b_x = mk_pred post_heap [var1] in
    (* here the alloc/free in the path are part of the LHS *)
    [ Comment ("same_heap_content_pre" , mk_equiv (mk_pred first_alloc [var1]) a_x);
      Comment ("implies_heap_content_post", mk_implies b_x (mk_pred last_alloc [var1])) ]

(* map: int -> id list *)
let get_constants model =
  let csts =
    IdMap.fold
      (fun id defs acc -> match defs with
        | [def] when def.Model.input = [] -> 
            (match def.Model.output with
            | Model.Int v ->
              let old = if Util.IntMap.mem v acc then Util.IntMap.find v acc else [] in
                Util.IntMap.add v (id::old) acc
            | _ -> acc)
        | _ -> acc)
      model
      Util.IntMap.empty
  in
    csts

let get_constants_terms model =
  let csts = get_constants model in
    List.flatten (snd (List.split (Util.IntMap.bindings csts)))
  

(* all equal *)
let mk_same lst =
  let repr = List.hd lst in
    List.fold_left
      (fun acc v -> (Sl.Eq (v, repr)) :: acc )
      []
      (List.tl lst)

(* all different *)
let mk_different lst =
  let rec different reprs = match reprs with
    | v :: vs -> (List.map (fun v2 -> Sl.Not (Sl.Eq (v, v2))) vs) @ (different vs)
    | [] -> []
  in
    different lst

(* all args satisfying the predicate: id list list
 * outer list is for each parameter
 * inner list is all the id that can get there (eq class)
 *)
let get_pred_all model csts pred_id =
  List.map
    (fun def -> List.map (fun i -> Util.IntMap.find i csts) def.Model.input)
    (List.filter
      (fun def -> (def.Model.output = Model.Bool true) )
      (IdMap.find pred_id model))

let get_pred_repr model csts pred_id =
  List.map (List.map List.hd) (get_pred_all model csts pred_id)

(*the succ fct (on repr ids) *)
let succ model csts =
  let reach_def = get_pred_repr model csts (Axioms.reach_id Sl.pts) in
  let reachable_from v =
    List.fold_left
      (fun acc args ->
        if List.nth args 0 = v then
          IdSet.add (List.nth args 1) acc 
        else
          acc
      )
      IdSet.empty
      reach_def
  in
  let reach_without v1 v2 =
    List.fold_left
      (fun acc args ->
        if List.nth args 0 = v1 && List.nth args 1 = v2 then
          IdSet.add (List.nth args 2) acc 
        else
          acc
      )
      IdSet.empty
      reach_def
  in
    (fun v ->
      Debug.msg ("make_frame: looking for successor of " ^ (str_of_ident v) ^ "\n");
      let candidates = IdSet.remove v (reachable_from v) in
      let pruned =
        IdSet.fold
          (fun v2 acc -> 
            let but_last = IdSet.remove v2 (reach_without v v2) in
              IdSet.diff acc but_last
          )
          candidates
          candidates
      in
        match IdSet.cardinal pruned with
        | 0 -> None
        | 1 -> Some (IdSet.choose pruned)
        | _ -> assert false
    )

(*
(* terms which forces the value of succ *)
let terms_for_succ model csts =
  let eqClasses = snd (List.split (Util.IntMap.bindings csts)) in
  let all_vars = List.flatten eqClasses in
  let repr = List.map List.hd eqClasses in
  let get_aliased v = List.find (List.mem v) eqClasses in
    (fun v s_v ->
      let vs = get_aliased v in
      let s_vs = get_aliased s_v in
      let others = List.filter (fun v -> not (List.mem v vs) && not (List.mem v s_vs)) all_vars in
      let all_terms =
        Util.flat_map
          (fun v ->
            Util.flat_map
              (fun s_v ->
                List.map
                  (fun o -> Axioms.reach Sl.pts (Form.mk_const v) (Form.mk_const s_v) (Form.mk_const o))
                  others
              )
              s_vs
          )
          vs
      in
        Form.mk_and all_terms
    )
*)

let weaken_model session eq_cls (model: Model.model) =
  (* the original eq classes: eq_cls *)
  (* the current eq classes *)
  let terms = List.map Form.mk_const (get_constants_terms model) in
  let cur_eq_cls = Prover.ModelGenerator.get_eq_classes_lst session terms in
  let s2 = SmtLib.push session in
  (* see if it is seprarable *)
  let assert_if_still_sat x y =
    if eq_cls x <> eq_cls y then
      begin
        let eq = Form.mk_eq x y in
        let s3 = SmtLib.push s2 in
          SmtLib.assert_form s3 eq;
          match SmtLib.is_sat s3 with
          | Some b ->
            let s4 = SmtLib.pop s3 in
              if b then SmtLib.assert_form s4 eq
          | None -> failwith "SmtLib.is_sat -> None"
      end
  in
  let rec try_separate_cls lst = match lst with
    | x :: xs -> List.iter (assert_if_still_sat x) xs
    | [] -> ()
  in
    List.iter try_separate_cls cur_eq_cls;
    let m2 = SmtLib.get_model s2 in
      ignore (SmtLib.pop s2);
      match m2 with
      | Some m -> m
      | None -> model

(*
let terms_for_blocking_clause model spatial =
  let csts = get_constants model in
  let eqClasses = snd (List.split (Util.IntMap.bindings csts)) in
  let get_aliased v = List.find (List.mem v) eqClasses in
  let ts = terms_for_succ model csts in
  let rec process t = match t with
    | Sl.PtsTo (a, b) ->
      let aliased_a = get_aliased a in
      let aliased_b = get_aliased b in
        Util.flat_map
          (fun x ->
            List.map (fun y -> Form.mk_eq (Form.mk_app Sl.pts [Form.mk_const x]) (Form.mk_const y) ) aliased_b)
          aliased_a
    | Sl.List (a, b) -> [ts a b]
    | Sl.SepConj lst -> Util.flat_map process lst
    | Sl.Emp -> []
    | _ -> failwith "terms_for_blocking_clause: expected only spatial terms"
  in
    failwith "TODO"
  (*
  let different_alloc_a = ... in
  let different_alloc_b = ... in
  let structure = process spatial in
    Form.smk_and (structure @ different_alloc_a @ different_alloc_b)
  *)
*)

(* make the frame from a model as described in the paper (section 8).*)
let make_frame heap_a last_alloc heap_b (model: Model.model) =
  if !Debug.verbose then
    begin
      print_endline "making frame for:";
      Model.print_model model
    end;
  
  
  (* pure part *)
  let csts = get_constants model in
  let eqClasses = snd (List.split (Util.IntMap.bindings csts)) in
  let representatives = List.map List.hd eqClasses in
  let same = List.flatten (List.map mk_same eqClasses) in
  let pure = Sl.And ((mk_different representatives) @ same) in
  (*TODO prune ~= implied by * *)

  (* spatial part *)
  let get_pred_def pred_id = get_pred_repr model csts pred_id in
  (* get the repr var for the nodes in heap_a but not in heap_b *)
  let vars_in heap =
    let heap_def = get_pred_def heap in
    let vars = List.map List.hd heap_def in
      List.fold_left (fun acc v -> IdSet.add v acc) IdSet.empty vars
  in
  (*let vars_a = vars_in heap_a in*)
  let vars_alloc = vars_in last_alloc in
  let vars_b = vars_in heap_b in
  let diff = IdSet.diff vars_alloc vars_b in
  (* get spatial term for a variable *)
  let succ = succ model csts in
  let get_spatial var = 
    let term = Form.mk_app Sl.pts [Form.mk_const var] in
      match Model.eval_term model term with
      | Some idx ->
        let var2 = List.hd (Util.IntMap.find idx csts) in
          Sl.PtsTo (Sl.pts, var, var2)
      | None ->
          (* no pts_to -> look for the successor in reach *)
          match succ var with
          | Some var2 -> Sl.List (var, var2)
          | None -> failwith "existential successor" (* Sl.PtsTo (var, fresh_ident "_") *)
  in
  let spatial = List.map get_spatial (IdSet.elements diff) in
  let spatial2 = match spatial with
    | [] -> Sl.Emp
    | [x] -> x
    | xs -> Sl.SepConj xs
  in
  let frame = Sl.SepConj [spatial2; pure] in
    Debug.msg ("frame is " ^ (Sl.to_string frame) ^ "\n");
    ((*frame,*) spatial2, pure)


let infer_frame_loop subst query =
  let last_alloc = last_alloc subst in
  let initial = Prover.ModelGenerator.initial_query query in
    match initial with
    | Some (session, _) ->
      let nodes = TermSet.elements (ground_terms query) in
      let eq_cls = Prover.ModelGenerator.get_eq_classes session nodes in
      let rec loop acc gen = match gen with
        | Some (generator, model) ->
          let model = weaken_model generator eq_cls model in
          (*
          if !Debug.verbose then
            begin
              print_endline "weakened model:";
              Model.print_model model
            end;
          *)
          let spatial, pure = make_frame pre_heap last_alloc post_heap model in
          let blocking = failwith "TODO older version" in (*terms_for_blocking_clause model spatial in*)
            Debug.msg ("blocking terms are " ^ (Form.string_of_form blocking) ^ "\n");
            loop ((spatial, pure) :: acc) (Prover.ModelGenerator.add_blocking_clause generator blocking)
        | None ->
          (* group by spatial ... *)
          let by_spatial =
            List.fold_left
              (fun acc (s, p) ->
                let old =
                  try Sl.SlMap.find s acc
                  with Not_found -> []
                in
                  Sl.SlMap.add s (p :: old) acc
              )
              Sl.SlMap.empty
              acc
          in
            List.map
              (fun (spatial, pures) -> Sl.mk_sep spatial (Sl.Or pures) )
              (Sl.SlMap.bindings by_spatial)

      in
        Some (loop [] initial)
    | None -> None


let mk_frame_query pre pathf post subst =
  let query = smk_and ( (Sl.make_axioms (Form.mk_and (pre :: post :: pathf))) ::
                        (same_heap_axioms subst) )
  in
  let _ = if !Debug.verbose then
    begin
      print_endline "frame query: ";
      print_form stdout query
    end
  in
    query

let infer_frame pre_sl path post_sl =
  let pre = Sl.to_lolli pre_heap pre_sl in
  let pathf, subst = ssa_partial IdMap.empty path in
  assert (List.length pathf = 1);
  let pathf = List.hd pathf in
  let post = Form.subst_id subst (Sl.to_lolli post_heap post_sl) in
  let query = mk_frame_query pre pathf post subst in
    infer_frame_loop subst query

(* Checks whether the frame exists *)
let is_frame_defined pre_sl pathf post_sl subst =
  let pre = Sl.to_lolli pre_heap pre_sl in
  let post = Form.subst_id subst (Sl.to_lolli_not_contained post_heap post_sl) in
  let query = mk_frame_query pre pathf post subst in
    match Prover.satisfiable query with
    | Some b -> not b
    | None -> failwith "is_frame_defined: Prover returned None"

let is_frame_defined_path pre_sl path post_sl =
  let pathf, subst = ssa_partial IdMap.empty path in
  assert (List.length pathf = 1);
  let pathf = List.hd pathf in
    is_frame_defined pre_sl pathf post_sl subst

(* TODO the normal for with disjunctions! *)
let combine_frames_with_f sll frames =
  if frames = [] then sll
  else Sl.normalize (Sl.mk_sep sll (Sl.Or frames))

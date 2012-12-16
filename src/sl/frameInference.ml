open Form
open Axioms
open Stmnt
open Entails

module IdMap = Form.IdMap
module IdSet = Form.IdSet

let implies_heap_content subst =
  (* heap axiom: B(x) => A(x)
   * if we have a path then we must compare
   * A(x) with first_alloc(x) and
   * B(x) with last_alloc(x)
   *)
  let first_alloc = alloc_id in
  let last_alloc =
    if IdMap.mem alloc_id subst
    then IdMap.find alloc_id subst
    else alloc_id
  in
  let a_x = mk_pred pre_heap [var1] in
  let b_x = mk_pred post_heap [var1] in
  (* here the alloc/free in the path are part of the LHS *)
    [ Comment ("same_heap_content_pre" , mk_equiv (mk_pred first_alloc [var1]) a_x);
      Comment ("implies_heap_content_post", mk_implies b_x (mk_pred last_alloc [var1])) ]

let trim_model (model: Model.model) =
  failwith "TODO remove the skolem cst ??"

(* make the frame from a model as described in the paper (section 8).*)
let make_frame heap_a heap_b (model: Model.model) =
  if !Debug.verbose then
    begin
      print_endline "making frame for: ";
      Model.print_model model
    end;
  (* pure part *)
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
  (* partition csts by values to get = and ~= *)
  let eqClasses =
    Util.IntMap.fold
      (fun _ vs acc -> vs :: acc)
      csts
      [] 
  in
  let representatives = List.map List.hd eqClasses in
  let same =
    List.fold_left2
      (fun acc vs repr -> (List.map (fun v -> Sl.Eq (v, repr)) (List.tl vs)) @ acc )
      []
      eqClasses
      representatives
  in
  let rec different acc reprs = match reprs with
    | v :: vs -> (List.map (fun v2 -> Sl.Not (Sl.Eq (v, v2))) vs) @ acc
    | _ -> acc
  in
  let pure = (different [] representatives) @ same in
  (* spatial part *)
  let get_pred_def pred_id = 
    List.map
      (fun def -> List.map (fun i -> List.hd (Util.IntMap.find i csts)) def.Model.input)
      (List.filter
        (fun def -> (def.Model.output = Model.Bool true) )
        (IdMap.find pred_id model))
  in
  (* get the var in heap_a but not in heap_b *)
  let vars_in heap =
    let heap_def = get_pred_def heap in
    let vars = List.map List.hd heap_def in
      List.fold_left (fun acc v -> IdSet.add v acc) IdSet.empty vars
  in
  let vars_a = vars_in heap_a in
  let vars_b = vars_in heap_b in
  let diff = IdSet.diff vars_a vars_b in
  (* get spatial term for a variable *)
  let reach_def = get_pred_def (Axioms.reach_id Sl.pts) in
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
  (*the succ fct as in the paper (page 14)*)
  let succ v =
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
    assert (IdSet.cardinal pruned = 1);
    IdSet.choose pruned
  in 
  let get_spatial var = 
    let term = Form.mk_app Sl.pts [Form.mk_const var] in
      match Model.eval_term model term with
      | Some idx ->
        let var2 = List.hd (Util.IntMap.find idx csts) in
          Sl.PtsTo (var, var2)
      | None ->
          (* no pts_to -> look for the successor in reach *)
          Sl.List (var, succ var)
  in
  let spatial = List.map get_spatial (Form.id_set_to_list diff) in
  let spatial2 = match spatial with
    | [] -> Sl.Emp
    | [x] -> x
    | xs -> Sl.SepConj xs
  in
  let frame = Sl.And (spatial2 :: pure) in
    Debug.msg ("frame is " ^ (Sl.to_string frame) ^ "\n");
    (frame, Sl.And pure)

let infer_frame_loop query =
  let rec loop acc gen = match gen with
    | Some (generator, model) ->
      let frame, pure = make_frame pre_heap post_heap model in
      let blocking = Sl.to_lolli post_heap pure in
        loop (frame :: acc) (Prover.ModelGenerator.add_blocking_clause generator blocking)
    | None -> acc
  in
  let initial = Prover.ModelGenerator.initial_query query in
    match initial with
    | Some _ -> Some (loop [] initial)
    | None -> None


let mk_frame_query pre pathf post subst =
  (* axioms from the logic *)
  let logic_axioms = List.flatten (make_axioms [ [pre]; pathf; [post]]) in
  
  (* query *)
  let query = smk_and ( pre :: post :: pathf @
                        (implies_heap_content subst) @
                        logic_axioms )
  in
  let _ = if !Debug.verbose then
    begin
      print_endline "query: ";
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
    infer_frame_loop query


let combine_frames_with_f sll frames =
  if frames = [] then sll
  else Sl.mk_sep sll (Sl.Or frames)

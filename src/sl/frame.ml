open Form
open FormUtil
open Axioms
open Entails

module IdMap = Form.IdMap
module IdSet = Form.IdSet


let implies_heap_content preh posth =
  (* heap axiom: B(x) => A(x)
   * if we have a path then we must compare
   * A(x) with first_alloc(x) and
   * B(x) with last_alloc(x) *)
    mk_subseteq (Sl.mk_loc_set preh) (Sl.mk_loc_set posth) 

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

let sym_to_id s = match s with
  | FreeSym v -> v
  | Null -> mk_ident "null"
  | _ -> failwith ("unexpected symbol: " ^ (str_of_symbol s))

let get_repr c_map s = sym_to_id (SymbolMap.find s c_map)

(*the succ fct (on repr ids) *)
let succ model =
  let reach_def = Model.defs_of ReachWO model in
  let f =
    match Model.eval_term model (Sl.to_field Sl.pts) with
    | Some t -> t
    | None -> failwith "Sl.pts is not defined"
  in
  let reachable_from v =
    List.fold_left
      (fun acc args ->
        if List.nth args.Model.input 0 = f &&
           List.nth args.Model.input 1 = v &&
           args.Model.output = (BoolConst true) then
          SymbolSet.add (List.nth args.Model.input 2) acc 
        else
          acc
      )
      SymbolSet.empty
      reach_def
  in
  let reach_without v1 v2 =
    List.fold_left
      (fun acc args ->
        if List.nth args.Model.input 0 = f &&
           List.nth args.Model.input 1 = v1 &&
           List.nth args.Model.input 2 = v2 &&
           args.Model.output = (BoolConst true) then
          SymbolSet.add (List.nth args.Model.input 3) acc 
        else
          acc
      )
      SymbolSet.empty
      reach_def
  in
    (fun v ->
      Debug.msg ("make_frame: looking for successor of " ^ (str_of_ident v) ^ "\n");
      match Model.eval_term model (Sl.mk_loc v) with
      | Some vc ->
        let candidates = SymbolSet.remove vc (reachable_from vc) in
        let pruned =
          SymbolSet.fold
            (fun v2 acc -> 
              let but_last = SymbolSet.remove v2 (reach_without vc v2) in
                SymbolSet.diff acc but_last
            )
            candidates
            candidates
        in
        let c_map = Model.const_map model in
          begin
          match SymbolSet.cardinal pruned with
            | 0 -> None
            | 1 -> Some (get_repr c_map (SymbolSet.choose pruned))
            | _ -> assert false
          end
      | None -> None
    )

(*
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
*)

let get_in_set model set_id =
  let decl = Model.defs_of (FreeSym set_id) model in
    List.fold_left
      (fun acc args ->
        if args.Model.output = (BoolConst true) then
          SymbolSet.add (List.hd args.Model.input) acc
        else acc
      )
      SymbolSet.empty
      decl

(* make the frame from a model as described in the paper (section 8).*)
let make_frame heap_a heap_b (model: Model.model) =
  if !Debug.verbose then
    begin
      print_endline "making frame for:";
      Model.print_model model
    end;
  
  
  let c_map = Model.const_map model in

  (* pure part *)
  let csts = Model.consts model in
  let eqClasses =
    SymbolSet.fold
      (fun sym acc ->
        let t = match Model.eval_term model (mk_const sym) with
          | Some t -> t
          | None -> failwith "symbol not defined"
        in
        let old = try SymbolMap.find t acc with Not_found -> [] in
          SymbolMap.add t ((sym_to_id sym) :: old) acc
      )
      csts
      SymbolMap.empty
  in
  let eqClasses = snd (List.split (SymbolMap.bindings eqClasses)) in
  let representatives = List.map List.hd eqClasses in
  let same = List.flatten (List.map mk_same eqClasses) in
  let pure = Sl.And ((mk_different representatives) @ same) in
  (*TODO prune ~= implied by * *)

  (* spatial part *)

  (* get the repr var for the nodes in heap_a but not in heap_b *)
  (*let vars_a = vars_in heap_a in*)
  let vars_a = get_in_set model heap_a in
  let vars_b = get_in_set model heap_b in
  let diff = SymbolSet.diff vars_a vars_b in
  (* get spatial term for a variable *)
  let succ = succ model in
  let get_spatial var = 
    let term = mk_read (Sl.to_field Sl.pts) (Sl.mk_loc var) in
      match Model.eval_term model term with
      | Some r ->
        let var2 = get_repr c_map r in
          Sl.PtsTo (Sl.pts, var, var2)
      | None ->
          (* no pts_to -> look for the successor in reach *)
          match succ var with
          | Some var2 -> Sl.List (var, var2)
          | None -> failwith "existential successor" (* Sl.PtsTo (var, fresh_ident "_") *)
  in
  let spatial =
    List.map
      (fun s -> get_spatial (sym_to_id s) )
      (SymbolSet.elements diff)
  in
  let spatial2 = match spatial with
    | [] -> Sl.Emp
    | [x] -> x
    | xs -> Sl.SepConj xs
  in
  let frame = Sl.SepConj [spatial2; pure] in
    Debug.msg ("frame is " ^ (Sl.to_string frame) ^ "\n");
    ((*frame,*) spatial2, pure)



let infer_frame_loop query preh posth =
  let initial = Prover.ModelGenerator.initial_query "frame" query in
    match initial with
    | Some (session, _) ->
      let rec loop acc gen = match gen with
        | Some (generator, model) ->
          (*
          let model = weaken_model generator eq_cls model in
          if !Debug.verbose then
            begin
              print_endline "weakened model:";
              Model.print_model model
            end;
          *)
          let spatial, pure = make_frame preh posth model in
          let blocking = Model.to_form model in
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


let mk_frame_query pre post preh posth =
  let query = smk_and [implies_heap_content preh posth; pre; post] in
  let _ = if !Debug.verbose then
    begin
      print_endline "frame query: ";
      print_form stdout query
    end
  in
    query

let infer_frame pre_sl post_sl =
  let preh = pre_heap () in
  let posth = post_heap () in
  let pre = Sl.to_grass preh pre_sl in
  let post = Sl.to_grass posth post_sl in
  let query = mk_frame_query pre post preh posth in
    infer_frame_loop query preh posth


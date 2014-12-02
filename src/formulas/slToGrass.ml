(* {5 Translate SL formulas to GRASS formulas} *)

open Grass
open Sl
open SlUtil

let close f =
  let aux_vars = Grass.IdSrtSet.elements (GrassUtil.sorted_free_vars f) in
  GrassUtil.mk_exists aux_vars (GrassUtil.nnf f)

(** Translate SL formula [f] to a GRASS formula where the set [domain] holds [f]'s footprint.
  * Atomic predicates in [f] are translated using the function [pred_to_form]. *)
let to_form pred_to_form domain f =
  let mk_error_msg (pos_opt, msg) f =
    match pos_opt with
    | Some pos -> GrassUtil.mk_error_msg (pos, msg) f
    | None -> f
  in
  let mk_srcpos pos_opt f = 
    match pos_opt with
    | Some pos -> GrassUtil.mk_srcpos pos f
    | None -> f
  in
  let fresh_dom d = mk_loc_set_var (GrassUtil.fresh_ident ("?" ^ fst d)) in
  let rec process_sep d f = 
    match f with
    | Pure (p, _) -> 
        [p, GrassUtil.mk_empty (Grass.Set Grass.Loc)]
    | Atom (Emp, _, pos) ->
        [GrassUtil.mk_true, GrassUtil.mk_empty (Grass.Set Grass.Loc)]
    | Atom (Region, [t], _) ->
        let domain = fresh_dom d in
        [GrassUtil.mk_eq domain t, domain]
    | Atom (Pred p, args, pos) ->
        let domain = fresh_dom d in
        let pdef = pred_to_form p args domain in
        [mk_srcpos pos pdef, domain]
    | SepOp (op, f1, f2, pos) ->
        let p = process_sep (GrassUtil.fresh_ident (fst d)) in
        let f1_tr = p f1 in
        let f2_tr = p f2 in
        let tr_product = 
          List.fold_left (fun acc s1 -> List.map (fun s2 -> (s1, s2)) f2_tr @ acc) [] f1_tr
        in
        let process trs ((f1_tr, f1_dom), (f2_tr, f2_dom)) =
           let domain = fresh_dom d in
           let aux_tr = 
             match op with
             | SepPlus -> []
             | SepStar -> 
                 let f1_and_f2_disjoint = 
                   mk_error_msg (pos, ProgError.mk_error_info "Specified regions are not disjoint")
                     (empty_t (GrassUtil.mk_inter [f1_dom; f2_dom]))
                 in
                 [mk_srcpos pos f1_and_f2_disjoint]
             | SepIncl -> [mk_srcpos pos (GrassUtil.mk_subseteq f1_dom f2_dom)]
           in
           let dom_def = 
             match op with
             | SepStar 
             | SepPlus -> GrassUtil.mk_eq domain (GrassUtil.mk_union [f1_dom; f2_dom])
             | SepIncl -> GrassUtil.mk_eq domain f2_dom
           in
           (GrassUtil.smk_and (dom_def :: f1_tr :: f2_tr :: aux_tr), domain) :: trs
        in
        List.fold_left process [] tr_product
    | BoolOp (Or, forms, _) ->
        Util.flat_map (process_sep d) forms
    | other -> failwith ("process_sep does not expect " ^ (string_of_form other))
  in
  let rec process_bool f = match f with
  | BoolOp (And, forms, _) ->
      let translated = List.map process_bool forms in
      GrassUtil.smk_and translated
  | BoolOp (Or, forms, _) ->
      let translated = List.map process_bool forms in
      GrassUtil.smk_or translated
  | BoolOp (Not, fs, _) ->
      let structure = process_bool (List.hd fs) in
      GrassUtil.mk_not (close structure)
  | Binder (Exists, vs, f, _) -> 
      process_bool f
  | Binder (Forall, vs, f, _) -> 
      failwith "Universal quantification in SL formulas is currently unsupported."
  | sep ->
      let d' = GrassUtil.fresh_ident "X" in
      let translated = process_sep d' sep in
      let pos = pos_of_sl_form sep in
      let process (tr, d) = 
        let d_eq_domain = 
          mk_error_msg (pos, ProgError.mk_error_info "Memory footprint at error location does not match this specification")
            (mk_srcpos pos (GrassUtil.mk_eq d domain))
        in
        GrassUtil.smk_and [d_eq_domain; tr]
      in
      GrassUtil.smk_or (List.map process translated)
  in
  process_bool f
    

let to_grass pred_to_form domain f =
  let translated = to_form pred_to_form domain (prenex_form f) in
  close translated


let to_grass_negated pred_to_form domain f =
  let f1 = prenex_form (mk_not f) in
  let translated = to_form pred_to_form domain f1 in
  close translated

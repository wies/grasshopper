(* Translate SL formulas to GRASS formulas *)

open Form
open Sl
open Symbols
open SlUtil

let close f =
  let aux_vars = Form.IdSrtSet.elements (FormUtil.sorted_free_vars f) in
  FormUtil.mk_exists aux_vars (FormUtil.nnf f)

(* translation that keeps the heap separated from the pointer structure *)
let to_form pred_to_form domain f =
  let mk_srcpos pos_opt f = match pos_opt with
  | Some pos -> FormUtil.mk_srcpos pos f
  | None -> f
  in
  let fresh_dom d = mk_loc_set_var (FormUtil.fresh_ident ("?" ^ fst d)) in
  let rec process_sep pol d f = 
    match f with
    | Pure (p, _) -> 
        [p, FormUtil.mk_empty (Form.Set Form.Loc)]
    | Atom (Emp, _, pos) ->
        [FormUtil.mk_true, FormUtil.mk_empty (Form.Set Form.Loc)]
    | Atom (Region, [t], _) ->
        let domain = fresh_dom d in
        [FormUtil.mk_eq domain t, domain]
    | Atom (Pred p, args, pos) ->
        let domain = fresh_dom d in
        let pdef = pred_to_form p args domain in
        [mk_srcpos pos pdef, domain]
    | SepOp (op, f1, f2, pos) ->
        let p = process_sep pol (FormUtil.fresh_ident (fst d)) in
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
             | SepStar -> [mk_srcpos pos (empty_t (FormUtil.mk_inter [f1_dom; f2_dom]))]
             | SepIncl -> [mk_srcpos pos (FormUtil.mk_subseteq f1_dom f2_dom)]
           in
           let dom_def = 
             match op with
             | SepStar 
             | SepPlus -> FormUtil.mk_eq domain (FormUtil.mk_union [f1_dom; f2_dom])
             | SepIncl -> FormUtil.mk_eq domain f2_dom
           in
           (FormUtil.smk_and (dom_def :: f1_tr :: f2_tr :: aux_tr), domain) :: trs
        in
        List.fold_left process [] tr_product
    | BoolOp (Or, forms, _) ->
        Util.flat_map (process_sep pol d) forms
    | other -> failwith ("process_sep does not expect " ^ (string_of_form other))
  in

  let rec process_bool pol f = match f with
    | BoolOp (And, forms, _) ->
      let translated = List.map (process_bool pol) forms in
      FormUtil.smk_and translated
    | BoolOp (Or, forms, _) ->
      let translated = List.map (process_bool pol) forms in
      FormUtil.smk_or translated
    | BoolOp (Not, fs, _) ->
      let structure = process_bool (not pol) (List.hd fs) in
      FormUtil.mk_not (close structure)
    | Binder (Exists, vs, f, _) -> 
        process_bool pol f
    | Binder (Forall, vs, f, _) -> 
        failwith "Universal quantification in SL formulas is currently unsupported."
    | sep ->
        let d' = FormUtil.fresh_ident "X" in
        let translated = process_sep pol d' sep in
        let pos = pos_of_sl_form sep in
        let process (tr, d) = 
          let d_eq_domain = 
            FormUtil.mk_comment "Memory footprint at error location does not match this specification" 
              (mk_srcpos pos (FormUtil.mk_eq d domain))
          in
          FormUtil.smk_and [tr; d_eq_domain]
        in
        FormUtil.smk_or (List.map process translated)
  in
  process_bool true f


let to_grass pred_to_form domain f =
  let translated = to_form pred_to_form domain (prenex_form f) in
  close translated


let to_grass_negated pred_to_form domain f =
  let f1 = prenex_form (mk_not f) in
  let translated = to_form pred_to_form domain f1 in
  close translated

(* {5 Translate SL formulas to GRASS formulas} *)

open Grass
open Sl
open SlUtil

let close f =
  let aux_vars = Grass.IdSrtSet.elements (GrassUtil.sorted_free_vars f) in
  GrassUtil.mk_exists aux_vars (GrassUtil.nnf f)

(** Translate SL formula [f] to a GRASS formula where the set [domain] holds [f]'s footprint.
  * Atomic predicates in [f] are translated using the function [pred_to_form]. *)
let to_form pred_to_form domains f =
  let struct_ids = struct_ids_from_domains domains in
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
  let fresh_dom d = mk_fresh_var_domains struct_ids ("?" ^ fst d) in
  let rec process_sep d f = 
    match f with
    | Pure (p, _) -> 
        [p, mk_empty_domains struct_ids]
    | Atom (Emp, _, pos) ->
        [GrassUtil.mk_true, mk_empty_domains struct_ids]
    | Atom (Region, [t], _) ->
        let prefix = "?" ^ (fst d) in
        let sid = GrassUtil.struct_id_of_sort (GrassUtil.element_sort_of_set t) in
        let domain = mk_empty_domains_except struct_ids sid prefix in
        [GrassUtil.mk_eq (IdMap.find sid domain) t, domain]
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
                   List.map
                     (mk_error_msg (pos, ProgError.mk_error_info "Specified regions are not disjoint"))
                     (mk_domains_disjoint f1_dom f2_dom)
                 in
                 List.map (mk_srcpos pos) f1_and_f2_disjoint
             | SepIncl ->
               let f1_in_f2 =
                 map_domains
                   (fun _ t1 t2 -> GrassUtil.mk_subseteq t1 t2)
                   f1_dom f2_dom
               in
               List.map (mk_srcpos pos) f1_in_f2
           in
           let dom_def = 
             match op with
             | SepStar | SepPlus ->
               mk_domains_eq
                 domain
                 (mk_union_domains f1_dom f2_dom)
             | SepIncl ->
               mk_domains_eq
                 domain
                 f2_dom
           in
           (GrassUtil.smk_and (f1_tr :: f2_tr :: dom_def @ aux_tr), domain) :: trs
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
        let eqs = mk_domains_eq domains d in
        let d_eqs_domain = 
          List.map
            (fun eq -> mk_error_msg
              (pos, ProgError.mk_error_info "Memory footprint at error location does not match this specification")
              (mk_srcpos pos eq))
            eqs
        in
        GrassUtil.smk_and (tr :: d_eqs_domain)
      in
      GrassUtil.smk_or (List.map process translated)
  in
  process_bool f
    

let to_grass pred_to_form domain f =
  let translated = to_form pred_to_form domain (prenex_form f) in
  close translated


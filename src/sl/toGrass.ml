(* Translate SL formulas to GRASS formulas *)

open Form
open Sl
open Symbols
open SlUtil

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
        ([p, FormUtil.mk_empty (Form.Set Form.Loc)], FormUtil.mk_true)
    | Atom (Emp, _, pos) ->
        [FormUtil.mk_true, FormUtil.mk_empty (Form.Set Form.Loc)], FormUtil.mk_true
    | Atom (Region, [t], _) ->
        let domain = fresh_dom d in
        [FormUtil.mk_true, domain], 
        FormUtil.mk_eq domain t
    | Atom (Pred p, args, pos) -> 
        (*let domain = fresh_dom d in*) 
        let domain = fresh_dom d in
        let structure, outputs = pred_to_form p args domain in
        [mk_srcpos pos structure, domain], FormUtil.smk_and outputs 
    | SepOp (op, f1, f2, pos) ->
        let p = process_sep pol (FormUtil.fresh_ident (fst d)) in
        let f1_structs, f1_defs = p f1 in
        let f2_structs, f2_defs = p f2 in
        let structs_product = 
          List.fold_left (fun acc s1 -> List.map (fun s2 -> (s1, s2)) f2_structs @ acc) [] f1_structs
        in
        let process (structs, defs) ((f1_struct, f1_dom), (f2_struct, f2_dom)) =
           let domain = fresh_dom d in
           let aux_struct = match op with
           | SepPlus -> []
           | SepStar -> [mk_srcpos pos (empty_t (FormUtil.mk_inter [f1_dom; f2_dom]))]
           | SepWand -> [mk_srcpos pos (empty_t (FormUtil.mk_inter [f1_dom; domain])); 
                         mk_srcpos pos (FormUtil.mk_subseteq f1_dom f2_dom)]
           | SepIncl -> [mk_srcpos pos (FormUtil.mk_subseteq f1_dom f2_dom)]
           in
           let dom_def = match op with
           | SepStar 
           | SepPlus -> FormUtil.mk_eq domain (FormUtil.mk_union [f1_dom; f2_dom])
           | SepWand -> FormUtil.mk_eq domain (FormUtil.mk_diff f2_dom f1_dom)
           | SepIncl -> FormUtil.mk_eq domain f2_dom
           in
           (FormUtil.smk_and (f1_struct :: f2_struct :: aux_struct), domain) :: structs, dom_def :: defs
        in
        let structs, defs = List.fold_left process ([], [f1_defs; f2_defs]) structs_product in
        structs, FormUtil.smk_and defs
    | BoolOp(Or, forms, _) ->
        let structs, defs = List.split (List.map (process_sep pol d) forms) in
        List.concat structs, FormUtil.smk_and defs
    | other -> failwith ("process_sep does not expect " ^ (string_of_form other))
  in

  let rec process_bool pol f = match f with
    | BoolOp (And, forms, _) ->
      let translated = List.map (process_bool pol) forms in
      let (translated_1, translated_2) = List.split translated in
        (FormUtil.smk_and translated_1, FormUtil.smk_and translated_2)
    | BoolOp (Or, forms, _) ->
      let translated = List.map (process_bool pol) forms in
      let (translated_1, translated_2) = List.split translated in
        (FormUtil.smk_or translated_1, FormUtil.smk_and translated_2)
    | BoolOp (Not, fs, _) ->
      let (structure, heap) = process_bool (not pol) (List.hd fs) in
        (FormUtil.mk_not structure, heap)
    | Binder (Exists, vs, f, _) -> process_bool pol f
    | Binder (Forall, vs, f, _) -> 
        failwith "Universal quantification in SL formulas is currently unsupported."
    | sep ->
        let d' = FormUtil.fresh_ident "X" in
        let struct_part, heap_part = process_sep pol d' sep in
        let pos = pos_of_sl_form sep in
        let process (str, d) = 
          FormUtil.mk_and [str; mk_srcpos pos (FormUtil.mk_eq d domain)]
        in
        FormUtil.smk_or (List.map process struct_part), heap_part
  in
  process_bool true f

let post_process f =
  let _ = if Debug.is_debug () then
    begin
      print_endline "Sl.to_grass(raw): ";
      print_endline (Form.string_of_form f);
      print_newline ()
    end
  in
  let aux_vars = Form.IdSrtSet.elements (FormUtil.sorted_free_vars f) in
  FormUtil.mk_exists aux_vars (FormUtil.nnf f)

let to_grass pred_to_form domain f =
  let structs, defs = to_form pred_to_form domain (prenex_form f) in
  post_process (FormUtil.smk_and [structs; defs])


let to_grass_negated pred_to_form domain f =
  let f1 = prenex_form (mk_not f) in
  let structs, defs = to_form pred_to_form domain f1 in
  post_process (FormUtil.smk_and [structs; defs])

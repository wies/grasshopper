(* Translate SL formulas to GRASS formulas *)

open Sl
open Symbols
open SlUtil

(*
let fresh_existentials f =
  let fct id t =
    if fst id = "_" 
    then FormUtil.mk_var ?srt:(FormUtil.sort_of t) (FormUtil.fresh_ident "?_")
    else t
  in
  subst_consts_fun fct f
*)

(* translation that keeps the heap separated from the pointer structure *)
let to_form pred_to_form domain f =
  let fresh_dom d = mk_loc_set_var (FormUtil.fresh_ident ("?" ^ fst d)) in
  let rec process_sep pol d f = 
    match f with
    | Pure p -> 
        ([p, FormUtil.mk_empty (Some (Form.Set Form.Loc))], FormUtil.mk_true)
    | Atom (Emp, _) ->
        [FormUtil.mk_true, FormUtil.mk_empty (Some (Form.Set Form.Loc))], FormUtil.mk_true
    | Atom (Region, [t]) ->
        let domain = fresh_dom d in
        [FormUtil.mk_true, domain], 
        FormUtil.mk_eq domain t
    | Atom (Pred p, args) -> 
        (*let domain = fresh_dom d in*) 
        let domain = fresh_dom d in
        let structure, outputs = pred_to_form p args domain in
        [structure, domain], FormUtil.smk_and outputs 
    | (SepStar forms as f)
    | (SepPlus forms as f) ->
        (*let ds = List.map (fun _ -> fd "sep" domain) forms in*)
        let translated = List.map (process_sep pol (FormUtil.fresh_ident (fst d))) forms in
        let translated_1, translated_2 = List.split translated in
        let translated_product = 
          match translated_1 with
          | [] -> []
          | ts :: tss ->
              List.fold_left 
                (fun acc ts1  -> Util.flat_map (fun ts2 ->  List.map (fun t -> t :: ts2) ts1) acc)
                (List.map (fun t -> [t]) ts) tss
        in
        let process (otranslated_1, translated_2) translated =
          let domain = fresh_dom d in
          let translated_1, dsc = List.split translated in
          let separation1 = FormUtil.mk_eq domain (FormUtil.mk_union dsc) in
          let separation2 =
            let rec pw_disj acc = function
              | _ :: [] 
              | [] -> acc
              | d1 :: dcs -> 
                 (*pw_disj (empty_t (FormUtil.mk_inter [d1; FormUtil.mk_union dcs]) :: acc) dcs *)
                 pw_disj (List.map (fun d2 -> empty_t (FormUtil.mk_inter [d2; d1])) dcs @ acc) dcs
            in pw_disj [] dsc
          in
          let heap_part = separation1 :: translated_2 in
          let struct_part = 
            match f with
            | SepStar _ -> FormUtil.smk_and (separation2 @ translated_1) 
            | SepPlus _ -> FormUtil.smk_and translated_1
            | _ -> failwith "impossible" (* for completeness of pattern matching *)
          in
          ((struct_part, domain) :: otranslated_1, heap_part)
        in 
        let struct_part, heap_part = List.fold_left process ([], translated_2) translated_product in
        struct_part, FormUtil.smk_and heap_part
    | SepWand (f1, f2) ->
        let f1_structs, f1_defs = process_sep pol (FormUtil.fresh_ident (fst d)) f1 in
        let f2_structs, f2_defs = process_sep pol (FormUtil.fresh_ident (fst d)) f2 in
        let f1_struct, f1_dom, f2_struct, f2_dom =
          match f1_structs, f2_structs with
          | [f1_struct, f1_dom], [f2_struct, f2_dom] -> f1_struct, f1_dom, f2_struct, f2_dom
          | _ -> failwith "process_sep: translation of disjunction below magic wand is not implemented."
        in
        let domain = fresh_dom d in
        [FormUtil.mk_and [f1_struct; f2_struct; empty_t (FormUtil.mk_inter [f1_dom; domain])], domain],
        FormUtil.smk_and [f1_defs; f2_defs; FormUtil.mk_eq f2_dom (FormUtil.mk_union [f1_dom; domain])]
    | Or forms ->
        let translated_1, translated_2 = List.split (List.map (process_sep pol d) forms) in
        List.concat translated_1, FormUtil.smk_and translated_2
    | other -> failwith ("process_sep does not expect " ^ (string_of_form other))
  in

  let rec process_bool pol f = match f with
    | And forms ->
      let translated = List.map (process_bool pol) forms in
      let (translated_1, translated_2) = List.split translated in
        (FormUtil.smk_and translated_1, FormUtil.smk_and translated_2)
    | Or forms ->
      let translated = List.map (process_bool pol) forms in
      let (translated_1, translated_2) = List.split translated in
        (FormUtil.smk_or translated_1, FormUtil.smk_and translated_2)
    | Not form ->
      let (structure, heap) = process_bool (not pol) form in
        (FormUtil.mk_not structure, heap)
    | sep ->
      let d' = FormUtil.fresh_ident "X" in
      let struct_part, heap_part = process_sep pol d' sep in
      let process (str, d) = FormUtil.mk_and [str; FormUtil.mk_eq d domain]
      in
      FormUtil.smk_or (List.map process struct_part), heap_part
  in
  (*process_bool true (fresh_existentials f)*)
  process_bool true f

let post_process f =
  let _ = if Debug.is_debug () then
    begin
      print_endline "Sl.to_grass(raw): ";
      Form.print_form stdout f;
      print_newline ()
    end
  in
  let aux_sets = Form.IdSrtSet.elements (FormUtil.sorted_free_vars f) in
  FormUtil.mk_exists aux_sets (FormUtil.nnf f)

let to_grass pred_to_form domain f =
  let (pointers, separations) = to_form pred_to_form domain f in
    post_process (FormUtil.smk_and [pointers; separations])

let to_grass_negated pred_to_form domain f =
  let (pointers, separations) = to_form pred_to_form domain (mk_not f) in
    post_process (FormUtil.smk_and [pointers; separations])

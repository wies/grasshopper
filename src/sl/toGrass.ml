open Sl
open Symbols
open SlUtil

(* translation to grass *)
let one_and_rest lst =
  let rec process acc1 acc2 lst = 
    match lst with
    | x :: xs -> process ((x, acc2 @ xs) :: acc1) (x :: acc2) xs
    | [] -> acc1
  in
  process [] [] lst

let fresh_existentials f =
  let fct id t =
    if fst id = "_" 
    then FormUtil.mk_var ?srt:(FormUtil.sort_of t) (FormUtil.fresh_ident "?_")
    else t
  in
 subst_consts_fun fct f

(* translation that keeps the heap separated from the pointer structure *)
let to_form pred_to_form set_fct domain f =
  let fd why d = FormUtil.fresh_ident ("?" ^ why ^ "_" ^(fst d)) in
  let rec process_sep pol d f = 
    match f with
    | Pure p -> 
        let domain = FormUtil.fresh_ident (fst d) in
        ([p, mk_loc_set_var domain], empty_var domain)
(* The following optimization for doubly-linked lists is deprecated
    | Atom (Pred s, [x1; x2; y1; y2]) when s = ("dlseg", 0) ->
        let domain = FormUtil.fresh_ident (fst d) in
        let part1 = reach x1 y1 in
        let part3 =
          Axioms.mk_axiom ("dll_" ^ Form.str_of_ident domain)
            (FormUtil.mk_implies (FormUtil.mk_and [ mk_domain domain Axioms.loc1;
                                                    mk_domain domain Axioms.loc2;
                                                    FormUtil.mk_eq (FormUtil.mk_read fpts Axioms.loc1) Axioms.loc2])
               (FormUtil.mk_eq (FormUtil.mk_read fprev_pts Axioms.loc2) Axioms.loc1)) in
        let part4 =
          FormUtil.mk_or [
          FormUtil.mk_and [ FormUtil.mk_eq x1 y1; FormUtil.mk_eq x2 y2];
          FormUtil.mk_and [ FormUtil.mk_eq (FormUtil.mk_read fprev_pts x1) x2;
                            FormUtil.mk_eq (FormUtil.mk_read fpts y2) y1;
                            mk_domain domain y2] ]
        in
        ( [FormUtil.mk_and ((if pol then [part3] else []) @ [part1;  part4]), mk_loc_set domain, IdSet.singleton domain],
          (get_symbol "dlseg").heap (mk_loc_set domain) [x1; x2; y1; y2]
         ) *)
    | Atom (Emp, _) ->
        let domain = FormUtil.fresh_ident (fst d) in
        [FormUtil.mk_true, mk_loc_set_var domain], empty_var domain
    | Atom (Region, [t]) ->
        let domain = FormUtil.fresh_ident (fst d) in
        [FormUtil.mk_true, mk_loc_set_var domain], 
        FormUtil.mk_eq (mk_loc_set_var domain) t
    | Atom (Pred p, args) -> 
        let domain = mk_loc_set_var (FormUtil.fresh_ident (fst d)) in
        let structure, footprint = pred_to_form p args domain in
        [structure, domain], footprint
    | SepConj forms ->
        (*let ds = List.map (fun _ -> fd "sep" domain) forms in*)
        let translated = List.map (process_sep pol (fd "sep" d)) forms in
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
          let domain = FormUtil.fresh_ident (fst d) in
          let translated_1, dsc = List.split translated in
          (*let dsc = List.map mk_loc_set ds in*)
          let separation1 = FormUtil.mk_eq (mk_loc_set_var domain) (FormUtil.mk_union dsc) in
          let separation2 =
            let rec pw_disj acc = function
              | d1 :: dcs -> pw_disj (List.map (fun d2 -> empty_t (FormUtil.mk_inter [d2; d1])) dcs @ acc) dcs
              | [] -> acc
            in pw_disj [] dsc
          in
          let heap_part = separation1 :: translated_2 in
          let struct_part = FormUtil.smk_and (separation2 @ translated_1) in
          ((struct_part, mk_loc_set_var domain) :: otranslated_1, heap_part)
        in 
        let struct_part, heap_part = List.fold_left process ([], translated_2) translated_product in
        struct_part, FormUtil.smk_and heap_part
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
      let d' = fd "leaf" domain in
      let struct_part, heap_part = process_sep pol d' sep in
      let process (str, d) =
        (* The following optimization for doubly-linked lists is deprecated
        let dll_axiom = 
          let in_domain =
            IdSet.fold
              (fun domain acc ->
                FormUtil.smk_or [acc; FormUtil.mk_and[ mk_domain domain Axioms.loc1; mk_domain domain Axioms.loc2]])
              domains
              FormUtil.mk_false
          in
          let ax_name = "dll_" ^ Form.str_of_ident domain in
          Axioms.mk_axiom ax_name
            (FormUtil.mk_implies
               (FormUtil.mk_and [in_domain; FormUtil.mk_eq (FormUtil.mk_read fpts Axioms.loc1) Axioms.loc2])
               (FormUtil.mk_eq (FormUtil.mk_read fprev_pts Axioms.loc2) Axioms.loc1))
        in *)
        FormUtil.mk_and [str; set_fct d (mk_loc_set domain)]
      in
      FormUtil.smk_or (List.map process struct_part), heap_part
  in
  process_bool true (fresh_existentials f)

let post_process f =
  let _ = if !Debug.verbose then
    begin
      print_endline "Sl.to_grass(raw): ";
      Form.print_form stdout f;
      print_newline ()
    end
  in
  let aux_sets = List.map (fun v -> (v, Form.Set Form.Loc)) (IdSet.elements (FormUtil.fv f)) in
  FormUtil.mk_exists aux_sets (FormUtil.nnf (FormTyping.typing f))

let to_grass pred_to_form domain f =
  let (pointers, separations) = to_form pred_to_form FormUtil.mk_eq domain f in
    post_process (FormUtil.smk_and [pointers; separations])

let to_grass_contained pred_to_form domain f = (* same structure and footprint not larger *)
  let (pointers, separations) = to_form pred_to_form FormUtil.mk_subseteq domain f in
    post_process (FormUtil.smk_and [pointers; separations])

let to_grass_not_contained pred_to_form domain f = (* different structure or larger footprint *)
  let (pointers, separations) = to_form pred_to_form FormUtil.mk_subseteq domain (mk_not f) in
    post_process (FormUtil.smk_and [pointers; separations])

let to_grass_negated pred_to_form domain f =
  let (pointers, separations) = to_form pred_to_form FormUtil.mk_eq domain (mk_not f) in
    post_process (FormUtil.smk_and [pointers; separations])

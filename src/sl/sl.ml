
type ident = Form.ident
let mk_ident = FormUtil.mk_ident
module IdMap = Form.IdMap
module IdSet = Form.IdSet
let ident_to_string = Form.str_of_ident

(* the next pointer *)
let pts = mk_ident "next"
let prev_pts = mk_ident "prev"

let to_field f = FormUtil.mk_free_const ?srt:(Some (Form.Fld Form.Loc)) f

let fpts = to_field pts
let fprev_pts = to_field prev_pts

(* data pointer *)
let data = mk_ident "data"
let fdata = FormUtil.mk_free_const ?srt:(Some (Form.Fld Form.Int)) data
let get_data l = FormUtil.mk_read fdata l

let mk_loc_set d =
  let tpe = Some (Form.Set Form.Loc) in
    FormUtil.mk_free_const ?srt:tpe d

let mk_loc d =
  if (fst d = "null") then FormUtil.mk_null
  else FormUtil.mk_free_const ?srt:(Some (Form.Loc)) d

let mk_const d =
  if (fst d = "null") then FormUtil.mk_null
  else FormUtil.mk_free_const d

type form =
  | Emp
  | Pure of Form.form
  | PtsTo of ident * ident * ident
  | List of ident * ident
  | SList of ident * ident
  | UList of ident * ident * ident
  | LList of ident * ident * ident
  | DList of ident * ident * ident * ident
  | SepConj of form list
  | Not of form
  | And of form list
  | Or of form list

module SlSet = Set.Make(struct
    type t = form
    let compare = compare
  end)

module SlMap = Map.Make(struct
    type t = form
    let compare = compare
  end)

let mk_emp = Emp
let mk_pure p = Pure p
let mk_true = mk_pure FormUtil.mk_true
let mk_false = mk_pure FormUtil.mk_false
let mk_eq a b = mk_pure (FormUtil.mk_eq (mk_const a) (mk_const b))
let mk_not a = Not a
let mk_pts a b = PtsTo (pts, a, b)
let mk_prev_pts a b = PtsTo (prev_pts, a, b)
let mk_ls a b = List (a, b)
let mk_sls a b = SList (a, b)
let mk_uls a b c = UList (a, b, c)
let mk_lls a b c = LList (a, b, c)
let mk_dls a b c d = DList (a, b, c, d)
let mk_and a b = And [a; b]
let mk_or a b = Or [a; b]
let mk_sep a b = 
  match (a, b) with
  | (Emp, _) -> b
  | (_, Emp) -> a
  | (SepConj aa, SepConj bb) -> SepConj (aa @ bb)
  | (a, SepConj bb) -> SepConj (a :: bb)
  | (SepConj aa, b) -> SepConj (aa @ [b]) 
  | _ -> SepConj [a; b]

let rec to_string f = match f with
  | Pure p -> Form.string_of_form p
  | Not t -> "~(" ^ (to_string t) ^")"
  | And lst -> "(" ^ (String.concat ") && (" (List.map to_string lst)) ^ ")"
  | Or lst ->  "(" ^ (String.concat ") || (" (List.map to_string lst)) ^ ")"
  | Emp -> "emp"
  | PtsTo (h, a, b) when h = pts -> (Form.str_of_ident a) ^ " |-> " ^ (Form.str_of_ident b)
  | PtsTo (h, a, b) when h = prev_pts -> (Form.str_of_ident a) ^ " |<- " ^ (Form.str_of_ident b)
  | PtsTo (h, a, b) -> (Form.str_of_ident a) ^ " |"^(ident_to_string h)^"> " ^ (Form.str_of_ident b)
  | List (a, b) -> "lseg(" ^ (Form.str_of_ident a) ^ ", " ^ (Form.str_of_ident b) ^ ")"
  | SList (a, b) -> "slseg(" ^ (Form.str_of_ident a) ^ ", " ^ (Form.str_of_ident b) ^ ")"
  | UList (a, b, c) -> "ulseg(" ^ (Form.str_of_ident a) ^ ", " ^ (Form.str_of_ident b) ^ ", " ^ (Form.str_of_ident c) ^ ")"
  | LList (a, b, c) -> "llseg(" ^ (Form.str_of_ident a) ^ ", " ^ (Form.str_of_ident b) ^ ", " ^ (Form.str_of_ident c) ^ ")"
  | DList (a, b, c, d) -> "dlseg(" ^ (String.concat ", " (List.map ident_to_string [a;b;c;d])) ^ ")"
  | SepConj lst -> "(" ^ (String.concat ") * (" (List.map to_string lst)) ^ ")"


let rec map_id fct f = match f with
  | Pure p -> Pure (FormUtil.map_id fct p)
  | Not t ->  Not (map_id fct t)
  | And lst -> And (List.map (map_id fct) lst)
  | Or lst -> Or (List.map (map_id fct) lst)
  | Emp -> Emp
  | PtsTo (h, a, b) -> PtsTo (h, fct a, fct b)
  | List (a, b) -> List (fct a, fct b)
  | SList (a, b) -> SList (fct a, fct b)
  | UList (a, b, c) -> UList (fct a, fct b, fct c)
  | LList (a, b, c) -> LList (fct a, fct b, fct c)
  | DList (a, b, c, d) -> DList (fct a, fct b, fct c, fct d)
  | SepConj lst -> SepConj (List.map (map_id fct) lst)

let subst_id subst f =
  let get id =
    try IdMap.find id subst with Not_found -> id
  in
    map_id get f

let rec has_prev f = match f with
  | Not t -> has_prev t
  | List _ | SList _ | UList _ | LList _ | Emp | Pure _ -> false
  | PtsTo (h, a, b) -> h = prev_pts
  | DList _ -> true
  | SepConj lst | And lst | Or lst -> 
    List.exists has_prev lst

(* translation to grass *)

let reachWoT a b c = FormUtil.mk_reachwo (fpts) a b c
let reachWo a b c = reachWoT (mk_loc a) (mk_loc b) (mk_loc c)
let btwnT a b c = FormUtil.mk_btwn (fpts) a b c
let btwn a b c = btwnT (mk_loc a) (mk_loc b) (mk_loc c)
let reachT a b = if !Config.use_btwn then btwnT a b b else reachWoT a b b
let reach a b = reachT (mk_loc a) (mk_loc b) 
let mk_domain d v = FormUtil.mk_elem v (mk_loc_set d)

let one_and_rest lst =
  let rec process acc1 acc2 lst = match lst with
    | x :: xs -> process ((x, acc2 @ xs) :: acc1) (x :: acc2) xs
    | [] -> acc1
  in
    process [] [] lst

let fresh_existentials f =
  let fct id =
    if (fst id) = "_" then FormUtil.fresh_ident "unamed_const"
    else id
  in
    map_id fct f

(* translation that keeps the heap separated from the pointer structure *)
let to_form set_fct domain f =
  let fd why d = FormUtil.fresh_ident ( why ^ "_" ^(fst d)) in
  (*let v = Axioms.var1 in
  let v2 = Axioms.var2 in*)
  let emptyset = FormUtil.mk_empty (Some (Form.Set Form.Loc)) in
  let empty_t domain = FormUtil.mk_eq emptyset domain in
  let empty domain = empty_t (mk_loc_set domain) in
  let list_set_def id1 id2 domain =
    FormUtil.mk_iff
      (FormUtil.smk_and 
         [if !Config.use_btwn 
          then btwnT (mk_loc id1) Axioms.loc1 (mk_loc id2)
          else reachWoT (mk_loc id1) Axioms.loc1 (mk_loc id2);
          FormUtil.mk_neq Axioms.loc1 (mk_loc id2)])
      (mk_domain domain Axioms.loc1)
  in
  let rec process_sep pol d f = 
    match f with
    | Pure p -> 
        let domain = FormUtil.fresh_ident (fst d) in
        ([p, mk_loc_set domain, IdSet.empty], empty domain)
    | Emp -> 
        let domain = FormUtil.fresh_ident (fst d) in
        ([FormUtil.mk_true, mk_loc_set domain, IdSet.empty], empty domain)
    | PtsTo (h, id1, id2) ->
        let domain = FormUtil.fresh_ident (fst d) in
        ([FormUtil.mk_eq (FormUtil.mk_read (to_field h) (mk_loc id1)) (mk_loc id2),
          mk_loc_set domain, IdSet.empty],
         FormUtil.mk_eq (mk_loc_set domain) (FormUtil.mk_setenum [mk_loc id1])
        )
    | List (id1, id2) ->
        let domain = FormUtil.fresh_ident (fst d) in
        ( [reach id1 id2, mk_loc_set domain, IdSet.empty],
          Axioms.mk_axiom 
            ("def_of_" ^ Form.str_of_ident domain) 
            (list_set_def id1 id2 domain)    
        )
    | SList (id1, id2) ->
        let domain = FormUtil.fresh_ident (fst d) in
        let part1 = reach id1 id2 in
        let part2 = 
          Axioms.mk_axiom ("sls_" ^ Form.str_of_ident domain)
            (FormUtil.mk_implies
              (FormUtil.mk_and [mk_domain domain Axioms.loc1;
                                mk_domain domain Axioms.loc2;
                                reachT Axioms.loc1 Axioms.loc2])
              (FormUtil.mk_leq (get_data Axioms.loc1) (get_data Axioms.loc2)))
        in
        let part3 =
          Axioms.mk_axiom 
            ("def_of_" ^ Form.str_of_ident domain) 
            (list_set_def id1 id2 domain)
        in
          ([FormUtil.mk_and [part1; part2], mk_loc_set domain, IdSet.empty], part3)
    | UList (id1, id2, id3) ->
        let domain = FormUtil.fresh_ident (fst d) in
        let part1 = reach id1 id2 in
        let part2 = 
          Axioms.mk_axiom ("uls_" ^ Form.str_of_ident domain)
            (FormUtil.mk_implies
              (FormUtil.mk_and [mk_domain domain Axioms.loc1])
              (FormUtil.mk_geq (get_data Axioms.loc1) (get_data (mk_loc id3))))
        in
        let part3 =
          Axioms.mk_axiom 
            ("def_of_" ^ Form.str_of_ident domain) 
            (list_set_def id1 id2 domain)
        in
          ([FormUtil.mk_and [part1; part2], mk_loc_set domain, IdSet.empty], part3)
    | LList (id1, id2, id3) ->
        let domain = FormUtil.fresh_ident (fst d) in
        let part1 = reach id1 id2 in
        let part2 = 
          Axioms.mk_axiom ("lls_" ^ Form.str_of_ident domain)
            (FormUtil.mk_implies
              (FormUtil.mk_and [mk_domain domain Axioms.loc1])
              (FormUtil.mk_leq (get_data Axioms.loc1) (get_data (mk_loc id3))))
        in
        let part3 =
          Axioms.mk_axiom 
            ("def_of_" ^ Form.str_of_ident domain) 
            (list_set_def id1 id2 domain)
        in
          ([FormUtil.mk_and [part1; part2], mk_loc_set domain, IdSet.empty], part3)
    | DList (x1, x2, y1, y2) ->
        let domain = FormUtil.fresh_ident (fst d) in
        let part1 = reach x1 y1 in
        let part2 =
          Axioms.mk_axiom 
            ("def_of_" ^ Form.str_of_ident domain) 
            (list_set_def x1 y1 domain)
        in
        let part3 =
          Axioms.mk_axiom ("dll_" ^ Form.str_of_ident domain)
            (FormUtil.mk_implies (FormUtil.mk_and [ mk_domain domain Axioms.loc1;
                                                    mk_domain domain Axioms.loc2;
                                                    FormUtil.mk_eq (FormUtil.mk_read fpts Axioms.loc1) Axioms.loc2])
               (FormUtil.mk_eq (FormUtil.mk_read fprev_pts Axioms.loc2) Axioms.loc1)) in
        let part4 =
          FormUtil.mk_or [
          FormUtil.mk_and [ FormUtil.mk_eq (mk_loc x1) (mk_loc y1); FormUtil.mk_eq (mk_loc x2) (mk_loc y2)];
          FormUtil.mk_and [ FormUtil.mk_eq (FormUtil.mk_read fprev_pts (mk_loc x1)) (mk_loc x2);
                            FormUtil.mk_eq (FormUtil.mk_read fpts (mk_loc y2)) (mk_loc y1);
                            mk_domain domain (mk_loc y2)] ]
        in
        ( [FormUtil.mk_and ((if pol then [part3] else []) @ [part1;  part4]), mk_loc_set domain, IdSet.singleton domain],
          part2          
         )
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
          let translated_1, dsc, domains = 
            List.fold_right
              (fun (t_1, d, odomains) (ts_1, dsc, domains) -> 
                (t_1 :: ts_1, d :: dsc, IdSet.union domains odomains))
              translated ([], [], IdSet.empty)
              
          in
          (*let dsc = List.map mk_loc_set ds in*)
          let separation1 = FormUtil.mk_eq (mk_loc_set domain) (FormUtil.mk_union dsc) in
          let separation2 =
            let rec pw_disj acc = function
              | d1 :: dcs -> pw_disj (List.map (fun d2 -> empty_t (FormUtil.mk_inter [d2; d1])) dcs @ acc) dcs
              | [] -> acc
            in pw_disj [] dsc
          in
          let heap_part = separation1 :: translated_2 in
          let struct_part = FormUtil.smk_and (separation2 @ translated_1) in
          ((struct_part, mk_loc_set domain, domains) :: otranslated_1, heap_part)
        in 
        let struct_part, heap_part = List.fold_left process ([], translated_2) translated_product in
        struct_part, FormUtil.smk_and heap_part
    | Or forms ->
        let translated_1, translated_2 = List.split (List.map (process_sep pol d) forms) in
        List.concat translated_1, FormUtil.smk_and translated_2
    | other -> failwith ("process_sep does not expect " ^ (to_string other))
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
      let process (str, d, domains) =
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
        in
        (FormUtil.mk_and (
         (if not (IdSet.is_empty domains) && not pol then [dll_axiom] else []) @
         [str; set_fct d (mk_loc_set domain)])) 
      in
      FormUtil.smk_or (List.map process struct_part), heap_part
  in
    process_bool true (fresh_existentials f)

let rec get_clauses f = match f with
  | Form.BoolOp (Form.And, lst) ->  List.flatten (List.map get_clauses lst)
  (*| Form.Comment (c, f) -> List.map (fun x -> Form.Comment (c,x)) (get_clauses f)*)
  | other -> [other]

let post_process f =
  let _ = if !Debug.verbose then
    begin
      print_endline "Sl.to_grass(raw): ";
      Form.print_form stdout f;
      print_newline ()
    end
  in
  FormUtil.nnf (FormTyping.typing f)

let to_grass domain f =
  let (pointers, separations) = to_form FormUtil.mk_eq domain f in
    post_process (FormUtil.smk_and [pointers; separations])

let to_grass_not_contained domain f = (* different structure or larger footprint *)
  let (pointers, separations) = to_form FormUtil.mk_subseteq domain (mk_not f) in
    post_process (FormUtil.smk_and [pointers; separations])

let to_grass_negated domain f =
  let (pointers, separations) = to_form FormUtil.mk_eq domain (mk_not f) in
    post_process (FormUtil.smk_and [pointers; separations])

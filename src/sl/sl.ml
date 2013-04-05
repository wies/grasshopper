
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

type symbol =
  { sym: string;
    arity: int;
    structure: ident (*domain*) -> ident list (*args*) -> Form.form;
    heap: ident (*domain*) -> ident list (*args*) -> Form.form;
  }

type form =
  | Pure of Form.form
  | Spatial of symbol * ident list
  | SepConj of form list
  | Not of form
  | And of form list
  | Or of form list

(* auxiliary functions *)
let reachWoT a b c = FormUtil.mk_reachwo (fpts) a b c
let reachWo a b c = reachWoT (mk_loc a) (mk_loc b) (mk_loc c)
let btwnT a b c = FormUtil.mk_btwn (fpts) a b c
let btwn a b c = btwnT (mk_loc a) (mk_loc b) (mk_loc c)
let reachT a b = if !Config.use_btwn then btwnT a b b else reachWoT a b b
let reach a b = reachT (mk_loc a) (mk_loc b) 
let mk_domain d v = FormUtil.mk_elem v (mk_loc_set d)
let emptyset = FormUtil.mk_empty (Some (Form.Set Form.Loc))
let empty_t domain = FormUtil.mk_eq emptyset domain
let empty domain = empty_t (mk_loc_set domain)
let list_set_def id1 id2 domain =
  FormUtil.mk_iff
    (FormUtil.smk_and 
       [if !Config.use_btwn 
        then btwnT (mk_loc id1) Axioms.loc1 (mk_loc id2)
        else reachWoT (mk_loc id1) Axioms.loc1 (mk_loc id2);
        FormUtil.mk_neq Axioms.loc1 (mk_loc id2)])
    (mk_domain domain Axioms.loc1)

(* the symbols *)

let emp   =
  { sym = "emp";
    arity = 0;
    structure = (fun _ _ -> FormUtil.mk_true);
    heap = (fun domain _ -> empty domain)
  }

let ptsTo =
  { sym = "ptsTo";
    arity = 3;
    structure = (fun _ args -> match args with
        | [h; id1; id2] -> FormUtil.mk_eq (FormUtil.mk_read (to_field h) (mk_loc id1)) (mk_loc id2)
        | _ -> failwith "wrong number of arguments");
    heap = (fun domain args ->  match args with
        | [_; id1; _] -> FormUtil.mk_eq (mk_loc_set domain) (FormUtil.mk_setenum [mk_loc id1])
        | _ -> failwith "wrong number of arguments");
  }

let lseg  =
  { sym = "lseg";
    arity = 2;
    structure = (fun _ args -> match args with
        | [id1; id2] ->  reach id1 id2
        | _ -> failwith "wrong number of arguments");
    heap = (fun domain args ->  match args with
        | [id1; id2] ->
            Axioms.mk_axiom 
              ("def_of_" ^ Form.str_of_ident domain) 
              (list_set_def id1 id2 domain)    
        | _ -> failwith "wrong number of arguments");
  }

let slseg =
  { sym = "slseg";
    arity = 2;
    structure = (fun domain args -> match args with
        | [id1; id2] -> 
            let part1 = reach id1 id2 in
            let part2 = 
              Axioms.mk_axiom ("sls_" ^ Form.str_of_ident domain)
                (FormUtil.mk_implies
                  (FormUtil.mk_and [mk_domain domain Axioms.loc1;
                                    mk_domain domain Axioms.loc2;
                                    reachT Axioms.loc1 Axioms.loc2])
                  (FormUtil.mk_leq (get_data Axioms.loc1) (get_data Axioms.loc2)))
            in
              FormUtil.mk_and [part1; part2]
        | _ -> failwith "wrong number of arguments");
    heap = (fun domain args ->  match args with
        | [id1; id2] ->
            Axioms.mk_axiom 
              ("def_of_" ^ Form.str_of_ident domain) 
              (list_set_def id1 id2 domain)    
        | _ -> failwith "wrong number of arguments");
  }

let ulseg =
  { sym = "ulseg";
    arity = 3;
    structure = (fun domain args -> match args with
        | [id1; id2; id3] -> 
            let part1 = reach id1 id2 in
            let part2 = 
              Axioms.mk_axiom ("uls_" ^ Form.str_of_ident domain)
                (FormUtil.mk_implies
                  (FormUtil.mk_and [mk_domain domain Axioms.loc1])
                  (FormUtil.mk_geq (get_data Axioms.loc1) (get_data (mk_loc id3))))
            in
              FormUtil.mk_and [part1; part2]
        | _ -> failwith "wrong number of arguments");
    heap = (fun domain args ->  match args with
        | [id1; id2; _] ->
            Axioms.mk_axiom 
              ("def_of_" ^ Form.str_of_ident domain) 
              (list_set_def id1 id2 domain)    
        | _ -> failwith "wrong number of arguments");
  }

let llseg =
  { sym = "llseg";
    arity = 3;
    structure = (fun domain args -> match args with
        | [id1; id2; id3] -> 
            let part1 = reach id1 id2 in
            let part2 = 
              Axioms.mk_axiom ("lls_" ^ Form.str_of_ident domain)
                (FormUtil.mk_implies
                  (FormUtil.mk_and [mk_domain domain Axioms.loc1])
                  (FormUtil.mk_leq (get_data Axioms.loc1) (get_data (mk_loc id3))))
            in
              FormUtil.mk_and [part1; part2]
        | _ -> failwith "wrong number of arguments");
    heap = (fun domain args ->  match args with
        | [id1; id2; _] ->
            Axioms.mk_axiom 
              ("def_of_" ^ Form.str_of_ident domain) 
              (list_set_def id1 id2 domain)    
        | _ -> failwith "wrong number of arguments");
  }

let uslseg =
  { sym = "uslseg";
    arity = 3;
    structure = (fun domain args -> match args with
        | [id1; id2; id3] -> 
            let part1 = reach id1 id2 in
            let part2 = 
              Axioms.mk_axiom ("usls_bound_" ^ Form.str_of_ident domain)
                (FormUtil.mk_implies
                  (FormUtil.mk_and [mk_domain domain Axioms.loc1])
                  (FormUtil.mk_geq (get_data Axioms.loc1) (get_data (mk_loc id3))))
            in
            let part3 =
              Axioms.mk_axiom ("usls_sort_" ^ Form.str_of_ident domain)
                (FormUtil.mk_implies
                  (FormUtil.mk_and [mk_domain domain Axioms.loc1;
                                    mk_domain domain Axioms.loc2;
                                    reachT Axioms.loc1 Axioms.loc2])
                  (FormUtil.mk_leq (get_data Axioms.loc1) (get_data Axioms.loc2)))
            in
              FormUtil.mk_and [part1; part2; part3]
        | _ -> failwith "wrong number of arguments");
    heap = (fun domain args ->  match args with
        | [id1; id2; _] ->
            Axioms.mk_axiom 
              ("def_of_" ^ Form.str_of_ident domain) 
              (list_set_def id1 id2 domain)    
        | _ -> failwith "wrong number of arguments");
  }

let lslseg =
  { sym = "lslseg";
    arity = 3;
    structure = (fun domain args -> match args with
        | [id1; id2; id3] -> 
            let part1 = reach id1 id2 in
            let part2 = 
              Axioms.mk_axiom ("lsls_bound_" ^ Form.str_of_ident domain)
                (FormUtil.mk_implies
                  (FormUtil.mk_and [mk_domain domain Axioms.loc1])
                  (FormUtil.mk_leq (get_data Axioms.loc1) (get_data (mk_loc id3))))
            in
            let part3 =
              Axioms.mk_axiom ("lsls_sort_" ^ Form.str_of_ident domain)
                (FormUtil.mk_implies
                  (FormUtil.mk_and [mk_domain domain Axioms.loc1;
                                    mk_domain domain Axioms.loc2;
                                    reachT Axioms.loc1 Axioms.loc2])
                  (FormUtil.mk_leq (get_data Axioms.loc1) (get_data Axioms.loc2)))
            in
              FormUtil.mk_and [part1; part2; part3]
        | _ -> failwith "wrong number of arguments");
    heap = (fun domain args ->  match args with
        | [id1; id2; _] ->
            Axioms.mk_axiom 
              ("def_of_" ^ Form.str_of_ident domain) 
              (list_set_def id1 id2 domain)    
        | _ -> failwith "wrong number of arguments");
  }

let dlseg =
  { sym = "dlseg";
    arity = 4;
    structure = (fun domain args -> match args with
        | [x1; x2; y1; y2] -> 
            let part1 = reach x1 y1 in
            let part2 =
              Axioms.mk_axiom ("dll_" ^ Form.str_of_ident domain)
                (FormUtil.mk_implies (FormUtil.mk_and [ mk_domain domain Axioms.loc1;
                                                        mk_domain domain Axioms.loc2;
                                                        FormUtil.mk_eq (FormUtil.mk_read fpts Axioms.loc1) Axioms.loc2])
                   (FormUtil.mk_eq (FormUtil.mk_read fprev_pts Axioms.loc2) Axioms.loc1)) in
            let part3 =
              FormUtil.mk_or [
              FormUtil.mk_and [ FormUtil.mk_eq (mk_loc x1) (mk_loc y1); FormUtil.mk_eq (mk_loc x2) (mk_loc y2)];
              FormUtil.mk_and [ FormUtil.mk_eq (FormUtil.mk_read fprev_pts (mk_loc x1)) (mk_loc x2);
                                FormUtil.mk_eq (FormUtil.mk_read fpts (mk_loc y2)) (mk_loc y1);
                                mk_domain domain (mk_loc y2)] ]
            in
              FormUtil.mk_and [part1; part2; part3]
        | _ -> failwith "wrong number of arguments");
    heap = (fun domain args ->  match args with
        | [id1; _; id2; _] ->
            Axioms.mk_axiom 
              ("def_of_" ^ Form.str_of_ident domain) 
              (list_set_def id1 id2 domain)    
        | _ -> failwith "wrong number of arguments");
  }


let symbols =
  [ emp;
    ptsTo;
    lseg;
    slseg;
    ulseg;
    llseg;
    uslseg;
    lslseg;
    dlseg ]

let find_def s = 
  try List.find (fun d -> s = d.sym) symbols
  with Not_found -> failwith "find_def: unknown symbol"

let arity s =
  try (List.find (fun d -> s = d.sym) symbols).arity
  with Not_found -> failwith "arity: unknown symbol"

let symbol_to_string s = 
  try (List.find (fun d -> s = d.sym) symbols).sym
  with Not_found -> failwith "symbol_to_string: unknown symbol"

let find_symbol s =
  try Some (List.find (fun d -> s = d.sym) symbols)
  with Not_found -> None

module SlSet = Set.Make(struct
    type t = form
    let compare = compare
  end)


let reachWoT a b c = FormUtil.mk_reachwo (fpts) a b c
let reachWo a b c = reachWoT (mk_loc a) (mk_loc b) (mk_loc c)
let btwnT a b c = FormUtil.mk_btwn (fpts) a b c
let btwn a b c = btwnT (mk_loc a) (mk_loc b) (mk_loc c)
let reachT a b = if !Config.use_btwn then btwnT a b b else reachWoT a b b
let reach a b = reachT (mk_loc a) (mk_loc b) 
let mk_domain d v = FormUtil.mk_elem v (mk_loc_set d)
let emptyset = FormUtil.mk_empty (Some (Form.Set Form.Loc))
let empty_t domain = FormUtil.mk_eq emptyset domain
let empty domain = empty_t (mk_loc_set domain)
let list_set_def id1 id2 domain =
  FormUtil.mk_iff
    (FormUtil.smk_and 
       [if !Config.use_btwn 
        then btwnT (mk_loc id1) Axioms.loc1 (mk_loc id2)
        else reachWoT (mk_loc id1) Axioms.loc1 (mk_loc id2);
        FormUtil.mk_neq Axioms.loc1 (mk_loc id2)])
    (mk_domain domain Axioms.loc1)
module SlMap = Map.Make(struct
    type t = form
    let compare = compare
  end)

let mk_pure p = Pure p
let mk_true = mk_pure FormUtil.mk_true
let mk_false = mk_pure FormUtil.mk_false
let mk_eq a b = mk_pure (FormUtil.mk_eq (mk_const a) (mk_const b))
let mk_not a = Not a
let mk_spatial s args = Spatial (s, args)
let mk_emp = mk_spatial emp []
let mk_pts a b = mk_spatial ptsTo [pts; a; b]
let mk_prev_pts a b = mk_spatial ptsTo [prev_pts; a; b]
let mk_ls a b = mk_spatial lseg [a; b]
let mk_dls a b c d = mk_spatial dlseg [a; b; c; d]
let mk_and a b = And [a; b]
let mk_or a b = Or [a; b]
let mk_sep a b = 
  match (a, b) with
  | (Spatial (e, []), _) when e.sym = emp.sym -> b
  | (_, Spatial (e, [])) when e.sym = emp.sym -> a
  | (SepConj aa, SepConj bb) -> SepConj (aa @ bb)
  | (a, SepConj bb) -> SepConj (a :: bb)
  | (SepConj aa, b) -> SepConj (aa @ [b]) 
  | _ -> SepConj [a; b]
let mk_sep_lst args = List.fold_left mk_sep mk_emp args

let mk_spatial_pred name args =
  match find_symbol name with
  | Some s ->
    if List.length args = s.arity then
      mk_spatial s args
    else
      failwith (name ^ " expect " ^(string_of_int (s.arity))^
                " found (" ^(String.concat ", " (List.map ident_to_string args))^ ")")
  | None -> failwith ("unknown spatial predicate " ^ name)

let rec to_string f = match f with
  | Pure p -> Form.string_of_form p
  | Not t -> "~(" ^ (to_string t) ^")"
  | And lst -> "(" ^ (String.concat ") && (" (List.map to_string lst)) ^ ")"
  | Or lst ->  "(" ^ (String.concat ") || (" (List.map to_string lst)) ^ ")"
  | Spatial (p, [h; a; b]) when p.sym = ptsTo.sym && h = pts -> (Form.str_of_ident a) ^ " |-> " ^ (Form.str_of_ident b)
  | Spatial (p, [h; a; b]) when p.sym = ptsTo.sym && h = prev_pts -> (Form.str_of_ident a) ^ " |<- " ^ (Form.str_of_ident b)
  | Spatial (s, []) -> s.sym
  | Spatial (s, args) -> s.sym ^ "(" ^ (String.concat ", " (List.map ident_to_string args)) ^ ")"
  | SepConj lst -> "(" ^ (String.concat ") * (" (List.map to_string lst)) ^ ")"


let rec map_id fct f = match f with
  | Pure p -> Pure (FormUtil.map_id fct p)
  | Not t ->  Not (map_id fct t)
  | And lst -> And (List.map (map_id fct) lst)
  | Or lst -> Or (List.map (map_id fct) lst)
  | Spatial (s, args) -> mk_spatial s (List.map fct args)
  | SepConj lst -> SepConj (List.map (map_id fct) lst)

let subst_id subst f =
  let get id =
    try IdMap.find id subst with Not_found -> id
  in
    map_id get f

let rec has_prev f = match f with
  | Not t -> has_prev t
  | Spatial (d, _) when d.sym = dlseg.sym -> true
  | Spatial (p, h :: _) -> p.sym = ptsTo.sym && h = prev_pts
  | Pure _ | Spatial _ -> false
  | SepConj lst | And lst | Or lst -> 
    List.exists has_prev lst

let rec has_data f = match f with
  | Not t -> has_data t
  | Spatial (d, _) when d.sym = slseg.sym ||
                        d.sym = llseg.sym ||
                        d.sym = ulseg.sym ||
                        d.sym = lslseg.sym ||
                        d.sym = uslseg.sym -> true
  | Pure _ | Spatial _ -> false
  | SepConj lst | And lst | Or lst -> 
    List.exists has_data lst

(* translation to grass *)

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
  let rec process_sep pol d f = 
    match f with
    | Pure p -> 
        let domain = FormUtil.fresh_ident (fst d) in
        ([p, mk_loc_set domain, IdSet.empty],
         empty domain)
    | Spatial (s, [x1; x2; y1; y2]) when s.sym = dlseg.sym ->
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
          FormUtil.mk_and [ FormUtil.mk_eq (mk_loc x1) (mk_loc y1); FormUtil.mk_eq (mk_loc x2) (mk_loc y2)];
          FormUtil.mk_and [ FormUtil.mk_eq (FormUtil.mk_read fprev_pts (mk_loc x1)) (mk_loc x2);
                            FormUtil.mk_eq (FormUtil.mk_read fpts (mk_loc y2)) (mk_loc y1);
                            mk_domain domain (mk_loc y2)] ]
        in
        ( [FormUtil.mk_and ((if pol then [part3] else []) @ [part1;  part4]), mk_loc_set domain, IdSet.singleton domain],
          dlseg.heap domain [x1; x2; y1; y2]
         )
    | Spatial (sym, args) -> 
        let domain = FormUtil.fresh_ident (fst d) in
          assert (List.length args = sym.arity);
          ( [ sym.structure domain args,
              mk_loc_set domain,
              IdSet.empty],
             sym.heap domain args )
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

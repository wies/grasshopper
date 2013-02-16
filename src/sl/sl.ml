
type ident = Form.ident
let mk_ident = FormUtil.mk_ident
module IdMap = Form.IdMap
module IdSet = Form.IdSet
let ident_to_string = Form.str_of_ident

(* the next pointer *)
let pts = mk_ident "next"
let prev_pts = mk_ident "prev"

let to_field f = FormUtil.mk_free_const ?srt:(Some (Form.Fld Form.Loc)) f

let mk_loc_set d =
  let tpe = Some (Form.Set Form.Loc) in
    FormUtil.mk_free_const ?srt:tpe d

let mk_loc d =
  if (fst d = "null") then FormUtil.mk_null
  else FormUtil.mk_free_const ?srt:(Some (Form.Loc)) d

let fpts = to_field pts
let fprev_pts = to_field prev_pts

let skolemCst = "SkolemCst"

type form =
  | Emp
  | Eq of ident * ident
  | PtsTo of ident * ident * ident
  | List of ident * ident
  | DList of ident * ident * ident * ident
  | SepConj of form list
  | BoolConst of bool
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


let mk_true = BoolConst true
let mk_false = BoolConst false
let mk_eq a b = Eq (a, b)
let mk_not a = Not a
let mk_pts a b = PtsTo (pts, a, b)
let mk_prev_pts a b = PtsTo (prev_pts, a, b)
let mk_ls a b = List (a, b)
let mk_dls a b c d = DList (a, b, c, d)
let mk_and a b = And [a; b]
let mk_or a b = Or [a; b]
let mk_sep a b = SepConj [a; b]

let rec to_string f = match f with
  | Not (Eq (e1, e2)) -> (ident_to_string e1) ^ " ~= " ^ (ident_to_string e2)
  | Eq (e1, e2) -> (ident_to_string e1) ^ " = " ^ (ident_to_string e2)
  | Not t -> "~(" ^ (to_string t) ^")"
  | And lst -> "(" ^ (String.concat ") && (" (List.map to_string lst)) ^ ")"
  | Or lst ->  "(" ^ (String.concat ") || (" (List.map to_string lst)) ^ ")"
  | BoolConst b -> string_of_bool b
  | Emp -> "emp"
  | PtsTo (h, a, b) when h = pts -> (Form.str_of_ident a) ^ " |-> " ^ (Form.str_of_ident b)
  | PtsTo (h, a, b) when h = prev_pts -> (Form.str_of_ident a) ^ " |<- " ^ (Form.str_of_ident b)
  | PtsTo (h, a, b) -> (Form.str_of_ident a) ^ " |"^(ident_to_string h)^"> " ^ (Form.str_of_ident b)
  | List (a, b) -> "lseg(" ^ (Form.str_of_ident a) ^ ", " ^ (Form.str_of_ident b) ^ ")"
  | DList (a, b, c, d) -> "dlseg(" ^ (String.concat ", " (List.map ident_to_string [a;b;c;d])) ^ ")"
  | SepConj lst -> "(" ^ (String.concat ") * (" (List.map to_string lst)) ^ ")"

let rec ids f = match f with
  | Eq (a, b) | PtsTo (_, a, b) | List (a, b) -> 
    IdSet.add a (IdSet.singleton b)
  | DList (a, b, c, d) -> List.fold_right IdSet.add [a; b; c] (IdSet.singleton d)
  | Not t -> ids t
  | And lst | Or lst | SepConj lst -> 
    List.fold_left
      (fun acc f2 -> IdSet.union acc (ids f2))
      IdSet.empty
      lst
  | BoolConst _ | Emp -> IdSet.empty

let rec normalize f = match f with
  | Eq (e1, e2) -> if e1 = e2 then BoolConst true else Eq (e1, e2)
  | Not t -> 
    begin
      match normalize t with
      | BoolConst b -> BoolConst (not b)
      | t2 -> Not t2
    end
  | And lst -> 
    let sub_forms =
      List.fold_left
        (fun acc t -> SlSet.add (normalize t) acc)
        SlSet.empty
        lst
    in
    let sub_forms = SlSet.remove (BoolConst true) sub_forms in
      if (SlSet.mem (BoolConst false) sub_forms) then BoolConst false
      else if (SlSet.cardinal sub_forms = 0) then BoolConst true
      else if (SlSet.cardinal sub_forms = 1) then SlSet.choose sub_forms
      else And (SlSet.elements sub_forms)
  | Or lst ->  
    let sub_forms =
      List.fold_left
        (fun acc t -> SlSet.add (normalize t) acc)
        SlSet.empty
        lst
    in
    let sub_forms = SlSet.remove (BoolConst false) sub_forms in
      if (SlSet.mem (BoolConst true) sub_forms) then BoolConst true
      else if (SlSet.cardinal sub_forms = 0) then BoolConst false
      else if (SlSet.cardinal sub_forms = 1) then SlSet.choose sub_forms
      else Or (SlSet.elements sub_forms)
  | SepConj lst -> 
    let lst2 = List.map normalize lst in
    let lst3 = List.filter (fun x -> x <> Emp) lst2 in
      SepConj lst3
  | BoolConst b -> BoolConst b
  | Emp -> Emp
  | PtsTo (h, a, b) -> PtsTo (h, a, b)
  | List (a, b) -> if a = b then Emp else List (a, b)
  | DList (a, b, c, d) -> DList (a, b, c, d) (* TODO can we do better ?? *)

let rec map_id fct f = match f with
  | Eq (e1, e2) -> Eq (fct e1, fct e2)
  | Not t ->  Not (map_id fct t)
  | And lst -> And (List.map (map_id fct) lst)
  | Or lst -> Or (List.map (map_id fct) lst)
  | BoolConst b -> BoolConst b
  | Emp -> Emp
  | PtsTo (h, a, b) -> PtsTo (h, fct a, fct b)
  | List (a, b) -> List (fct a, fct b)
  | DList (a, b, c, d) -> DList (fct a, fct b, fct c, fct d)
  | SepConj lst -> SepConj (List.map (map_id fct) lst)

let subst_id subst f =
  let get id =
    try IdMap.find id subst with Not_found -> id
  in
    map_id get f

let rec has_prev f = match f with
  | Not t -> has_prev t
  | Eq _ | BoolConst _ | List _ | Emp -> false
  | PtsTo (h, a, b) -> h = prev_pts
  | DList _ -> true
  | SepConj lst | And lst | Or lst -> 
    List.exists has_prev lst

(* translation to grass/grass *)

let mk_exists = FormUtil.mk_exists
let mk_forall = FormUtil.mk_forall

(*let cst = FormUtil.mk_free_const*)
let reachWoT a b c = FormUtil.mk_reachwo (fpts) a b c
let reachWo a b c = reachWoT (mk_loc a) (mk_loc b) (mk_loc c)
let reach a b = reachWo a b b
let mk_domain d v = FormUtil.mk_elem v (mk_loc_set d)

let one_and_rest lst =
  let rec process acc1 acc2 lst = match lst with
    | x :: xs -> process ((x, acc2 @ xs) :: acc1) (x :: acc2) xs
    | [] -> acc1
  in
    process [] [] lst

let fresh_existentials f =
  let fct id =
    if (fst id) = "_" then FormUtil.fresh_ident "_"
    else id
  in
    map_id fct f

(* translation that keep the heap separation separated from the pointer structure *)
let to_form set_fct domain f =
  let fd why d = FormUtil.fresh_ident ( why ^ "_" ^(fst d)) in
  (*let v = Axioms.var1 in
  let v2 = Axioms.var2 in*)
  let empty_t domain = FormUtil.mk_eq (FormUtil.mk_empty (Some (Form.Set Form.Loc))) domain in
  let empty domain = empty_t (mk_loc_set domain) in
  let rec process_sep pol domain f = match f with
    | BoolConst b -> (FormUtil.mk_bool b, empty domain, IdSet.empty)
    | Not (Eq (id1, id2)) -> (FormUtil.mk_neq (mk_loc id1) (mk_loc id2), empty domain, IdSet.empty) (*TODO are id1, id2 always locations ? *)
    | Eq (id1, id2) -> (FormUtil.mk_eq (mk_loc id1) (mk_loc id2), empty domain, IdSet.empty) (*TODO are id1, id2 always locations ? *)
    | Emp -> (FormUtil.mk_true, empty domain, IdSet.empty)
    | PtsTo (h, id1, id2) ->
        ( FormUtil.mk_eq (FormUtil.mk_read (to_field h) (mk_loc id1)) (mk_loc id2),
          FormUtil.mk_eq (mk_loc_set domain) (FormUtil.mk_setenum [mk_loc id1]),
          IdSet.empty
        )
    | List (id1, id2) ->
        ( reach id1 id2,
          mk_forall [Axioms.l1] (
            FormUtil.mk_iff
              (FormUtil.smk_and [
                reachWoT (mk_loc id1) Axioms.loc1 (mk_loc id2);
                FormUtil.mk_neq Axioms.loc1 (mk_loc id2) ] )
              (mk_domain domain Axioms.loc1) ),
          IdSet.empty
        )
    | DList (x1, x2, y1, y2) ->
      let part1 = reach x1 y1 in
      let part2 =
        mk_forall [Axioms.l1]
          (FormUtil.mk_iff (mk_domain domain Axioms.loc1)
                             (FormUtil.mk_and [ reachWoT (mk_loc x1) Axioms.loc1 (mk_loc y1);
                                                FormUtil.mk_neq Axioms.loc1 (mk_loc y1)])) in
      let part3 =
        mk_forall [Axioms.l1; Axioms.l2]
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
        ( FormUtil.mk_and ((if pol then [part3] else []) @ [part1;  part4]),
          part2,
          IdSet.singleton domain
        )
    | SepConj forms ->
      let ds = List.map (fun _ -> fd "sep" domain) forms in
      let translated = List.map2 (process_sep pol) ds forms in
      let (translated_1, translated_2, domains) = 
        List.fold_left
          (fun (ts_1, ts_2, ds) (t_1, t_2, domains) -> (t_1 :: ts_1, t_2 :: ts_2, IdSet.union domains ds))
          ([], [], IdSet.empty)
          translated 
      in
      let dsc = List.map mk_loc_set ds in
      let separation =
        (FormUtil.mk_eq (mk_loc_set domain) (FormUtil.mk_union dsc)) ::
        (Util.flat_map (fun d1 -> Util.flat_map (fun d2 -> if d1 <> d2 then [empty_t (FormUtil.mk_inter [d1; d2])] else []) dsc) dsc)
      in
      let heap_part = FormUtil.smk_and (separation @ translated_2) in
      let struct_part = FormUtil.smk_and translated_1 in
        (struct_part, heap_part, domains)
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
      let (str, heap, domains) = process_sep pol d' sep in
      let dll_axiom = 
        let in_domain =
          IdSet.fold
            (fun domain acc ->
              FormUtil.smk_or [acc; FormUtil.mk_and[ mk_domain domain Axioms.loc1; mk_domain domain Axioms.loc2]])
            domains
            FormUtil.mk_false
        in
          mk_forall
            [Axioms.l1 ; Axioms.l2]
            (FormUtil.mk_implies
              (FormUtil.mk_and [in_domain; FormUtil.mk_eq (FormUtil.mk_read fpts Axioms.loc1) Axioms.loc2])
              (FormUtil.mk_eq (FormUtil.mk_read fprev_pts Axioms.loc2) Axioms.loc1))
      in
        (FormUtil.mk_and (
          (if not pol then [dll_axiom] else []) @
          [str; set_fct (mk_loc_set d') (mk_loc_set domain)]),
         heap)
  in
    process_bool true (fresh_existentials f)

(* assumes NNF *)
let skolemize f =
  let stack = ref [] in
  let top = ref [] in
  let available = ref [] in

  let push () =
    stack := !top :: !stack;
    top := []
  in
  let pop () =
    available := !top @ !available;
    top := List.hd !stack;
    stack := List.tl !stack
  in

  let has_candidate args_tpe tpe =
    let rec find acc lst = match lst with
      | ((id, args, ret) as x) :: xs ->
        if List.for_all2 (=) args args_tpe && ret = tpe then
           begin
             available := acc @ xs;
             Some id
           end
        else
          find (x :: acc) xs
      | [] -> None
    in
      find [] !available
  in

  let fresh u_vars tpe = 
    let mk_v (id, srt) = FormUtil.mk_var ?srt:(Some srt) id in
    let srts = List.map snd u_vars in
    let id = match has_candidate srts tpe with
      | Some id -> id
      | None -> FormUtil.fresh_ident skolemCst
    in
    let term = FormUtil.mk_free_app ?srt:(Some tpe) id (List.map mk_v u_vars) in
      top := (id, srts, tpe) :: !top;
      term
  in

  let rec process u_vars subst f = match f with
    | Form.Atom a -> Form.Atom (FormUtil.subst_term subst a)
    | Form.BoolOp (Form.Or, fs) -> 
      let forms2 =
        List.map
          (fun f ->
            push ();
            let f2 = process u_vars subst f in
              pop ();
              f2)
          fs
      in
        Form.BoolOp (Form.Or, forms2)
    | Form.BoolOp (other, fs) -> 
      let forms2 = List.map (process u_vars subst) fs in
        Form.BoolOp (other, forms2)
    | Form.Binder (Form.Forall, vs, f2, an) -> 
      let f3 = process (vs @ u_vars) subst f2 in
        Form.Binder (Form.Forall, vs, f3, an)
    | Form.Binder (Form.Exists, vs, f2, an) -> 
      let new_terms = List.map (fun (id, tp) -> fresh u_vars tp) vs in
      let subst2 =
        List.fold_left2
          (fun acc (v, _) t -> IdMap.add v t acc)
          subst
          vs
          new_terms
      in
      let f3 = process u_vars subst2 f2 in
        (*do not throw away the annotations *)
        if an = [] then f3
        else Form.Binder (Form.Exists, [], f3, an)

  in
    process [] IdMap.empty f

(* pull the axioms at the top level.
 * assumes: nnf, skolemized
 *)
let positive_with_top_Lvl_axioms f =
(*let equisat_with_topLvl_axioms f =
  let fresh () = Form.mk_pred (FormUtil.fresh_ident "equisat") [] in*)
  let fresh () = FormUtil.mk_pred (FormUtil.fresh_ident "positive") [] in
  let rec process f = match f with
    | (Form.Atom _) as a -> (a, [])
    | (Form.BoolOp (Form.Not, [Form.Atom _])) as n -> (n, [])
    | Form.BoolOp (Form.Not, _) -> failwith "positive_with_top_Lvl_axioms: formula not in NNF"
    | Form.BoolOp (bop, fs) -> 
      let forms2, accs = List.split (List.map process fs) in
        (Form.BoolOp (bop, forms2), List.flatten accs)
    | Form.Binder (bdr, [], f2, an) -> (*annotations only*)
      let (f3, acc) = process f2 in
        (Form.Binder (bdr, [], f3, an), acc)
    | Form.Binder (Form.Exists, vs, f2, an) -> failwith "f has not been skolemized"
    | Form.Binder (Form.Forall, vs, f2, an) -> 
      let p = fresh () in
      let part1 = FormUtil.mk_implies (FormUtil.mk_not p) f2 in
      (*let part2 = Form.mk_or [skolemize (nnf (Form.mk_not f)); p] in*)
        (p, [part1](*; part2]*))
  in
  let top_level f = match f with
    | Form.Atom _ -> (f, [])
    | Form.Binder _ -> (f, [])
    | other -> process other
  in
  let clauses = match f with
    | Form.BoolOp (Form.And, fs) -> fs
    | other -> [other]
  in
  let (f2s, accs) = List.split (List.map top_level clauses) in
    FormUtil.smk_and (f2s  @ (List.flatten accs))


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
    positive_with_top_Lvl_axioms (
      skolemize (
        FormUtil.nnf f ) )

let to_grass domain f =
  let (pointers, separations) = to_form FormUtil.mk_eq domain f in
    post_process (FormUtil.smk_and [pointers; separations])

let to_grass_not_contained domain f = (* different structure or larger footprint *)
  let (pointers, separations) = to_form FormUtil.mk_subseteq domain (mk_not f) in
    post_process (FormUtil.smk_and [pointers; separations])

let to_grass_negated domain f =
  let (pointers, separations) = to_form FormUtil.mk_eq domain (mk_not f) in
    post_process (FormUtil.smk_and [pointers; separations])

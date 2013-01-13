
type ident = Form.ident
let mk_ident = Form.mk_ident
module IdMap = Form.IdMap
module IdSet = Form.IdSet
let ident_to_string = Form.str_of_ident

(* the next pointer *)
let pts = mk_ident "sl_next"
let prev_pts = mk_ident "sl_prev"

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

(* translation to lolli/grass *)

let exists = "exists"
let forall = "forall"

let mk_exists f = Form.Comment (exists, f)
let mk_forall f = Form.Comment (forall, f)

let cst = Form.mk_const
let reachWoT a b c = Axioms.reach pts a b c
let reachWo a b c = reachWoT (cst a) (cst b) (cst c)
let reach a b = reachWo a b b
let mk_domain d v = Form.mk_pred d [v]

let one_and_rest lst =
  let rec process acc1 acc2 lst = match lst with
    | x :: xs -> process ((x, acc2 @ xs) :: acc1) (x :: acc2) xs
    | [] -> acc1
  in
    process [] [] lst

(* helpers for sets *)
let set_in set v = Form.mk_pred set [v]

let set_included set1 set2 =
  Form.mk_implies (set_in set1 Axioms.var1) (set_in set2 Axioms.var1)

let set_equiv set1 set2 =
  Form.mk_equiv (set_in set1 Axioms.var1) (set_in set2 Axioms.var1)

let set_disjoint set1 set2 =
  Form.mk_or [Form.mk_not (set_in set1 Axioms.var1); Form.mk_not (set_in set2 Axioms.var1)]

let set_union union set1 set2 =
  Form.mk_equiv (set_in union Axioms.var1) (Form.mk_or [(set_in set1 Axioms.var1); (set_in set2 Axioms.var1)])

let set_inter inter set1 set2 =
  Form.mk_equiv (set_in inter Axioms.var1) (Form.mk_and [(set_in set1 Axioms.var1); (set_in set2 Axioms.var1)])

let set_difference diff set1 set2 =
  Form.mk_equiv (set_in diff Axioms.var1) (Form.mk_and [(set_in set1 Axioms.var1); Form.mk_not (set_in set2 Axioms.var1)])
(*********************)

(* translation that keep the heap separation separated from the pointer structure *)
let to_form set_fct domain f =
  let fd why d = Form.fresh_ident ( why ^ "_" ^(fst d)) in
  let v = Axioms.var1 in
  let v2 = Axioms.var2 in
  let empty domain = mk_forall (Form.mk_not (mk_domain domain v)) in
  let rec process_sep domain f = match f with
    | BoolConst b -> (Form.BoolConst b, empty domain)
    | Not (Eq (id1, id2)) -> (Form.mk_neq (cst id1) (cst id2), empty domain)
    | Eq (id1, id2) -> (Form.mk_eq (cst id1) (cst id2), empty domain)
    | Emp -> (Form.BoolConst true, empty domain)
    | PtsTo (h, id1, id2) ->
        ( Form.mk_eq (Form.mk_app h [cst id1]) (cst id2),
          mk_forall (Form.mk_equiv (Form.mk_eq (cst id1) v) (mk_domain domain v))
        )
    | List (id1, id2) ->
        ( reach id1 id2,
          mk_forall (
            Form.mk_equiv (
              Form.mk_and [
                reachWoT (cst id1) v (cst id2);
                Form.mk_neq v (cst id2)
              ]; )
            (mk_domain domain v) )
        )
    | DList (x1, x2, y1, y2) ->
      let part1 = reach x1 y1 in
      let part2 = mk_forall (Form.mk_equiv (mk_domain domain v) (Form.mk_and [reachWoT (cst x1) v (cst y1); Form.mk_neq v (cst y1)])) in
      let part3 = mk_forall (Form.mk_implies (Form.mk_and [mk_domain domain v; mk_domain domain v2; Form.mk_eq (Form.mk_app pts [v]) v2]) (Form.mk_eq (Form.mk_app prev_pts [v2]) v)) in
      let part4 = Form.mk_or [
                    Form.mk_and [Form.mk_eq (cst x1) (cst x2); Form.mk_eq (cst y1) (cst y2)];
                    Form.mk_and [ Form.mk_eq (Form.mk_app prev_pts [cst x1]) (cst x2);
                                  Form.mk_eq (Form.mk_app pts [cst y2]) (cst y1);
                                  mk_domain domain (cst y2)] ]
      in
        ( Form.mk_and [part1; part3; part4],
          part2
        )
    | SepConj forms ->
      let ds = List.map (fun _ -> fd "sep" domain) forms in
      let translated = List.map2 process_sep ds forms in
      let (translated_1, translated_2) = List.split translated in
      let dsP = List.map (fun d -> mk_domain d v) ds in
      let d = mk_domain domain v in
      let sepration =
        mk_forall (Form.mk_and (
            (Form.mk_implies d (Form.mk_or dsP))
            :: (List.map (fun (x, xs) -> Form.mk_implies x (Form.mk_and (d :: (List.map Form.mk_not xs)))) (one_and_rest dsP))
          )
        )
      in
      let heap_part = Form.mk_and (sepration :: translated_2) in
      let struct_part = Form.smk_and translated_1 in
        (struct_part, heap_part)
    | other -> failwith ("process_sep does not expect " ^ (to_string other))
  in

  let rec process_bool f = match f with
    | And forms ->
      let translated = List.map process_bool forms in
      let (translated_1, translated_2) = List.split translated in
        (Form.smk_and translated_1, Form.smk_and translated_2)
    | Or forms ->
      let translated = List.map process_bool forms in
      let (translated_1, translated_2) = List.split translated in
        (Form.smk_or translated_1, Form.smk_and translated_2)
    | Not form ->
      let (structure, heap) = process_bool form in
        (Form.mk_not structure, heap)
    | sep ->
      let d' = fd "leaf" domain in
      let (str, heap) = process_sep d' sep in
        (Form.mk_and [str; mk_forall (set_fct d' domain)], heap)
  in
    process_bool f

let nnf f =
  let rec process negate f = match f with
    | Form.BoolConst b -> Form.BoolConst (negate <> b)
    | Form.Pred _ as p -> if negate then Form.mk_not p else p
    | Form.Eq _ as eq -> if negate then Form.mk_not eq else eq
    | Form.Not form -> process (not negate) form
    | Form.And forms ->
      let forms2 = List.map (process negate) forms in
        if negate then Form.mk_or forms2
        else Form.mk_and forms2
    | Form.Or forms -> 
      let forms2 = List.map (process negate) forms in
        if negate then Form.mk_and forms2
        else Form.mk_or forms2
    | Form.Comment (c, form) ->
      let form2 = process negate form in
      let c2 =
        if negate && c = exists then forall
        else if negate && c = forall then exists
        else c
      in
        Form.mk_comment c2 form2
  in
    process false f

(*
let negate_ignore_quantifiers f =
  let rec process negate f = match f with
    | Form.BoolConst b -> Form.BoolConst (negate <> b)
    | Form.Pred _ as p -> if negate then Form.mk_not p else p
    | Form.Eq _ as eq -> if negate then Form.mk_not eq else eq
    | Form.Not form -> process (not negate) form
    | Form.And forms ->
      let forms2 = List.map (process negate) forms in
        if negate then Form.mk_or forms2
        else Form.mk_and forms2
    | Form.Or forms -> 
      let forms2 = List.map (process negate) forms in
        if negate then Form.mk_and forms2
        else Form.mk_or forms2
    | Form.Comment (c, form) ->
      let form2 = process negate form in
        Form.mk_comment c form2
  in
    process true f
*)

(* assumes no quantifier alternation *)
let skolemize f =
  let fresh () = cst (Form.fresh_ident skolemCst) in
  let rec process subst f = match f with
    | Form.BoolConst _ as b -> b
    | Form.Eq _ | Form.Pred _ -> Form.subst subst f
    | Form.Not form -> Form.mk_not (process subst form)
    | Form.And forms -> Form.smk_and (List.map (process subst) forms) 
    | Form.Or forms -> Form.smk_or (List.map (process subst) forms)
    | Form.Comment (c, form) ->
        if c = exists then
          let subst2 =
            IdSet.fold
              (fun v acc -> IdMap.add v (fresh ()) acc) 
              (Form.fv form)
              subst
          in
            process subst2 form
        else if c = forall then 
          let vs = Form.fv form in
          let subst2 = IdSet.fold IdMap.remove vs subst in
            Form.mk_comment c (process subst2 form)
        else 
          Form.mk_comment c (process subst form)
  in
    process IdMap.empty f

(* pull the axioms at the top level.
 * assumes: nnf, skolemized
 *)
let positive_with_top_Lvl_axioms f =
(*let equisat_with_topLvl_axioms f =
  let fresh () = Form.mk_pred (Form.fresh_ident "equisat") [] in*)
  let fresh () = Form.mk_pred (Form.fresh_ident "positive") [] in
  let rec process f = match f with
    | Form.BoolConst _ | Form.Eq _ | Form.Pred _ -> (f, [])
    | Form.Not f2 -> 
      let (f3, acc) = process f2 in
        (Form.mk_not f3, acc)
    | Form.And forms -> 
      let forms2, accs = List.split (List.map process forms) in
        (Form.mk_and forms2, List.flatten accs)
    | Form.Or forms ->
      let forms2, accs = List.split (List.map process forms) in
        (Form.mk_or forms2, List.flatten accs)
    | Form.Comment (c, form) ->
        if c = exists then
          failwith "f has not been skolemized"
        else if c = forall then 
          let p = fresh () in
          let part1 = Form.mk_or [Form.mk_not p; form] in
          (*let part2 = Form.mk_or [skolemize (nnf (Form.mk_not f)); p] in*)
            (p, [part1](*; part2]*))
        else 
          let (f2, acc) = process form in
            (Form.mk_comment c f2, acc)
  in
  let top_level f = match f with
    | Form.BoolConst _ | Form.Eq _ | Form.Pred _ -> (f, [])
    | Form.Comment (c, form) when c = exists -> (f, [])
    | Form.Comment (c, form) when c = forall -> (f, [])
    | other -> process other
  in
  let clauses = match f with
    | Form.And lst -> lst
    | other -> [other]
  in
  let (f2s, accs) = List.split (List.map top_level clauses) in
    Form.smk_and (f2s  @ (List.flatten accs))

let to_lolli domain f =
  let (pointers, separations) = to_form set_equiv domain f in
    positive_with_top_Lvl_axioms (Form.smk_and [pointers; separations])

let to_lolli_with_axioms domain f =
  let f2 = to_lolli domain f in
  let ax = List.flatten (Axioms.make_axioms [[f2]]) in
    Form.smk_and (f2 :: ax)

let to_lolli_not_contained domain f = (* different structure or larger footprint *)
  let (pointers, separations) = to_form set_included domain (mk_not f) in
    positive_with_top_Lvl_axioms (skolemize (nnf (Form.smk_and [pointers; separations])))
(*
  let domain2 = Form.fresh_ident ("in_" ^(fst domain)) in
  let sk_var = Form.mk_const (Form.fresh_ident "skolemCst") in
  let different_domain = Form.mk_and [Form.mk_not (mk_domain domain sk_var); (mk_domain domain2 sk_var)] in
  let (pointers, separations) = to_form domain2 f in
  let pointers = negate_ignore_quantifiers pointers in
    positive_with_top_Lvl_axioms (Form.smk_and [Form.smk_or [different_domain; pointers]; separations])
*)    

let to_lolli_negated domain f =
  (*
  let domain2 = Form.fresh_ident ("neg_" ^(fst domain)) in
  let sk_var = Form.mk_const (Form.fresh_ident "skolemCst") in
  let different_domain = Form.mk_not (Form.mk_equiv (mk_domain domain sk_var) (mk_domain domain2 sk_var)) in
  *)
  let (pointers, separations) = to_form set_equiv domain (mk_not f) in
    positive_with_top_Lvl_axioms (skolemize (nnf (Form.smk_and [pointers; separations])))

let to_lolli_negated_with_axioms domain f =
  let f2 = to_lolli_negated domain f in
  let ax = List.flatten (Axioms.make_axioms [[f2]]) in
    Form.smk_and (f2 :: ax)

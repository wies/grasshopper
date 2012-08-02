
type ident = Form.ident
let mk_ident = Form.mk_ident

module Pure =
  struct
    type t =
      | Eq of ident * ident
      | Not of t
      | And of t list
      | Or of t list
      | BoolConst of bool

    let compare: t -> t -> int = compare

    let rec to_string f = match f with
      | Eq (e1, e2) -> (Form.str_of_ident e1) ^ " = " ^ (Form.str_of_ident e2)
      | Not t -> "~(" ^ (to_string t) ^")"
      | And lst -> "(" ^ (String.concat ") && (" (List.map to_string lst)) ^ ")"
      | Or lst ->  "(" ^ (String.concat ") || (" (List.map to_string lst)) ^ ")"
      | BoolConst b -> string_of_bool b

    let mk_true = BoolConst true
    let mk_false = BoolConst false

    let mk_and = function
      | [] -> mk_true
      | [f] -> f
      | fs -> And fs

    let mk_or = function
      | [] -> mk_false
      | [f] -> f
      | fs -> Or fs

    let mk_not = function
      | BoolConst b -> BoolConst (not b)
      | f -> Not f

    let mk_eq a b = Eq (a, b)

    let simplify form =
      failwith "TODO"

    let nnf form =
      let rec process negate f = match f with
        | Eq (e1, e2) as eq -> if negate then Not eq else eq
        | Not t -> process (not negate) t
        | And lst -> if negate then Or (List.map (process negate) lst) else And (List.map (process negate) lst)
        | Or lst -> if negate then And (List.map (process negate) lst) else Or (List.map (process negate) lst)
        | BoolConst b -> BoolConst (if negate then not b else b)
      in
        process false form

    (** convert a formula to CNF.
     * Expensive (exponential).
     * Assume NNF.
     *)
    let cnf form =
      let rec process t = match t with
        | And lst -> List.flatten (List.map process lst)
        | Or lst ->
          let merge cnf1 cnf2 =
            List.flatten (List.map (fun x -> List.map (fun y -> x @ y) cnf2) cnf1)
          in
          let rec iterate acc l (*: list list list == disj of conj of disj *) =
            match l with
            | x :: xs -> iterate (merge x acc) xs
            | [] -> acc
          in
          let sub_cnf = List.map process lst in
            iterate [[]] sub_cnf
        | _ as t -> [[t]]
      in
        mk_and (List.map mk_or (process form))

    (** convert a formula to CNF.
     * Expensive (exponential).
     * Assume NNF.
     *)
    let dnf form =
      let rec process t = match t with
        | Or lst -> List.flatten (List.map process lst)
        | And lst ->
          let merge dnf1 dnf2 =
            List.flatten (List.map (fun x -> List.map (fun y -> x @ y) dnf2) dnf1)
          in
          let rec iterate acc l (*: list list list == conj of disj of conj *) =
            match l with
            | x :: xs -> iterate (merge x acc) xs
            | [] -> acc
          in
          let sub_dnf = List.map process lst in
            iterate [[]] sub_dnf
        | _ as t -> [[t]]
      in
        mk_or (List.map mk_and (process form))

    let rec variables form = match form with
      | Eq (e1, e2) -> Form.IdSet.add e2 (Form.IdSet.singleton e1)
      | Not t -> variables t
      | And lst | Or lst ->
        List.fold_left
          (fun acc f -> Form.IdSet.union acc (variables f))
          Form.IdSet.empty
          lst
      | BoolConst b -> Form.IdSet.empty

  end

module Spatial =
  struct
    type t =
      | Emp
      | PtsTo of ident * ident
      | List of ident * ident
      | SepConj of t list
      | Conj of t list
      | Disj of t list

    let compare: t -> t -> int = compare

    let rec to_string f = match f with
      | Emp -> "emp"
      | PtsTo (a, b) -> (Form.str_of_ident a) ^ " |-> " ^ (Form.str_of_ident b)
      | List (a, b) -> "lseg(" ^ (Form.str_of_ident a) ^ ", " ^ (Form.str_of_ident b) ^ ")"
      | SepConj lst -> "(" ^ (String.concat ") * (" (List.map to_string lst)) ^ ")"
      | Conj lst -> "(" ^ (String.concat ") && (" (List.map to_string lst)) ^ ")"
      | Disj lst -> "(" ^ (String.concat ") || (" (List.map to_string lst)) ^ ")"

    let mk_pts a b = PtsTo (a, b)

    let mk_ls a b = List (a, b)

    let mk_conj = function
      | [] -> Emp
      | [f] -> f
      | fs -> Conj fs

    let mk_sep = function
      | [] -> Emp
      | [f] -> f
      | fs -> SepConj fs

    let mk_disj = function
      | [] -> Emp
      | [f] -> f
      | fs -> Disj fs

    (** Normalize a spatial formula. The resulting formula is in DNF and
     *  inside the conjunct the first level is the cunjunctions and the lowest
     *  level contains the separating conjunctions. *)
    let normalize form =
      let rec pick_one_in_each sub = match sub with
        | x :: xs ->
          let suffixes = pick_one_in_each xs in
            List.flatten (List.map (fun prefix -> List.map (fun suffix -> prefix :: suffix) suffixes) x)
        | [] -> [[]]
      in
      let dnf f =
        let rec process t = match t with
          | Disj lst -> List.flatten (List.map process lst)
          | Conj lst ->
            let sub_dnf = List.map process lst in
              List.map mk_conj (pick_one_in_each sub_dnf)
          | SepConj lst ->
            let sub_dnf = List.map process lst in
              List.map mk_sep (pick_one_in_each sub_dnf)
          | _ as t -> [t]
        in
          mk_disj (process f)
      in
      let distr_sep_conj f =
        let rec process t = match t with
          | Disj lst -> failwith "distr_sep_conj: not expected Disj"
          | Conj lst -> List.flatten (List.map process lst)
          | SepConj lst ->
            let sub = List.map process lst in
              List.map mk_sep (pick_one_in_each sub)
          | _ as t -> [t]
        in
          mk_conj (process f)
      in
        match dnf form with
        | Disj lst -> Disj (List.map distr_sep_conj lst)
        | elt -> distr_sep_conj elt

    let rec variables form = match form with
      | Emp -> Form.IdSet.empty
      | PtsTo (a, b) -> Form.IdSet.add b (Form.IdSet.singleton a)
      | List (a, b) -> Form.IdSet.add b (Form.IdSet.singleton a)
      | SepConj lst | Conj lst | Disj lst ->
        List.fold_left
          (fun acc f -> Form.IdSet.union acc (variables f))
          Form.IdSet.empty
          lst
  end

type sl_form = Pure.t * Spatial.t

let to_string (pure, spatial) =
  (Pure.to_string pure) ^ "   " ^ (Spatial.to_string spatial)

let normalize (pure, spatial) =
  (Pure.nnf pure, Spatial.normalize spatial)

(* the next pointer *)
let pts = ("sl_pts", 0)

(* Assumes (pure, spatial) are normalized. *)
let to_form (pure, spatial) =
  (* auxiliary fct *)
  let cst = Form.mk_const in
  let eq a b = Form.mk_eq (cst a) (cst b) in
  let reachWoT a b c = Axioms.reach pts a b c in
  let reachWo a b c = reachWoT (cst a) (cst b) (cst c) in
  let reachT a b = reachWoT a b b in
  let reach a b = reachWo a b b in
  let join a b = Axioms.jp pts (cst a) (cst b) in
  (* pure part *)
  let rec convert_pure p = match p with
    | Pure.Eq (e1, e2) -> Form.mk_eq (cst e1) (cst e2)
    | Pure.Not t -> Form.mk_not (convert_pure t)
    | Pure.And lst -> Form.smk_and (List.map convert_pure lst)
    | Pure.Or lst -> Form.smk_or (List.map convert_pure lst)
    | Pure.BoolConst b -> if b then Form.mk_true else Form.mk_false 
  in
  (* spatial part *)
  let rec convert_spatial s = match s with
    | Spatial.Emp -> Form.mk_true
    | Spatial.PtsTo (a, b) -> Form.mk_pred pts [cst a; cst b]
    | Spatial.List (a, b) -> reach a b
    | Spatial.SepConj lst ->
      (*TODO disjointness also for |-> *)
      (* disjointness conditions for ls(e_1, e_2) * ls(e_1', e_2') :
       *   (e_1 = join(e_1', e_1) \/ reachWo(e_1, e_2, join(e_1',e_1))) /\
       *   (e_1' = join(e_1, e_1') \/ reachWo(e_1', e_2', join(e_1,e_1'))) /\
       *   (e_1 = e_1' ==> e_1 = e_2 \/ e_1' = e_2')        *)
      let mk_disj e1 e2 e1p e2p =
        Form.mk_and [
          Form.mk_or [Form.mk_eq (cst e1) (join e1p e1); reachWoT (cst e1) (cst e2) (join e1p e1)];
          Form.mk_or [Form.mk_eq (cst e1p) (join e1 e1p); reachWoT (cst e1p) (cst e2p) (join e1 e1p)];
          Form.mk_or [Form.mk_not (eq e1 e1p); eq e1 e2; eq e1p e2p]
        ]
      in
      let lists = List.flatten (List.map (function Spatial.List (e1, e2) -> [(e1, e2)]| _ -> []) lst) in
      let rec mk_disjs acc lst = match lst with
        | (e1, e2) :: xs ->
          let d = List.map (fun (e1p, e2p) -> mk_disj e1 e2 e1p e2p) xs in
            mk_disjs (d @ acc) xs
        | [] -> acc
      in
      let part1 = List.map convert_spatial lst in
      let part2 = mk_disjs [] lists in
        Form.smk_and (part1 @ part2)
    | Spatial.Conj lst -> Form.smk_and (List.map convert_spatial lst)
    | Spatial.Disj lst -> Form.smk_or (List.map convert_spatial lst)
  in
  (* tightness conditions:
   *  \forall x. \/_{e_1, e_2} (reachWo(e_1, x, e_2) /\ reach(x, e_2))
   * TODO this might break if the set of variables is empty ??? *)
  let vars = List.map cst (Form.id_set_to_list (Spatial.variables spatial)) in
  let mk_axiom_part e1 e2 = Form.mk_and [(reachWoT e1 Axioms.var1 e2); (reachT Axioms.var1 e2)] in
  let tightness_axiom = Form.mk_or (List.flatten (List.map (fun e1 -> List.map (mk_axiom_part e1) vars) vars)) in
  let fp = convert_pure pure in
  let fs = convert_spatial spatial in
  let f = Form.mk_and [fp; fs] in
  let usual_axioms = match Axioms.add_axioms [[f]] with
    | [a] -> a
    | _ -> failwith "add_axioms did not return a single element"
  in
    Form.mk_and (f :: tightness_axiom :: usual_axioms)

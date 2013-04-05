open Form
open FormUtil
open Axioms
open SimpleLanguage

type subst = ident IdMap.t
type signatures = (sort option) IdMap.t

let subst_to_string subst =
  String.concat "\n"
    (List.map
      (fun (id1, id2) ->
        (str_of_ident id1) ^ " -> " ^ (str_of_ident id2)
      )
      (IdMap.bindings subst) )

type kind = Step of form * subst * signatures
          | Branch of form
          | Axiom of form
          (*TODO a cut thing (drop everything before?? for calls, loops, ...) *)

let is_step k = match k with
  | Step _ -> true
  | _ -> false
let is_branch k = match k with
  | Branch _ -> true
  | _ -> false
let is_axiom k = match k with
  | Axiom _ -> true
  | _ -> false

let kind_to_string k = match k with
  | Step (f, _, _) -> "Step: " ^ (string_of_form f)
  | Branch f -> "Branch: " ^ (string_of_form f)
  | Axiom f -> "Axiom: " ^ (string_of_form f)

type t = kind list

let empty = []

let to_string stack =
  String.concat "\n" (List.map kind_to_string stack)

let step stack f s t = (Step (f, s, t)) :: stack

let axiom stack f = (Axiom f) :: stack

let push stack f = (Branch f) :: stack

(** Returns (a, b) where a is the part that was poped, b is the new stack.*)
let pop stack =
  let rec pop1 acc stack = match stack with
    | ((Step _) as x) :: xs -> pop1 (x :: acc) xs
    | ((Axiom _) as x):: xs -> pop1 (x :: acc) xs
    | ((Branch _) as x) :: xs -> ((List.rev (x :: acc)), xs)
    | [] -> failwith "popping an empty stack."
  in
    pop1 [] stack

let fold_topdown = List.fold_left
let fold_bottomup = List.fold_right
let map = List.map
let filter = List.filter

let get_form stack =
  let get k = match k with
    | Step (f, _, _) -> f
    | Branch f -> f
    | Axiom f -> f
  in
    map get stack

let conditions stack =
    get_form (filter is_branch stack)

let axioms stack =
    get_form (filter is_axiom stack)

let steps stack =
    get_form (filter is_step stack)

let get_subst stack =
  try 
    match List.find is_step stack with
    | Step (_, s, _) -> s
    | _ -> failwith "is_step ?!?"
  with Not_found -> IdMap.empty

let get_sign stack =
  try 
    match List.find is_step stack with
    | Step (_, _, s) -> s
    | _ -> failwith "is_step ?!?"
  with Not_found -> IdMap.empty

(** makes an axiom depends on the currents decisions *)
let guard_axiom stack f =
  mk_implies (mk_and (conditions stack)) f

let guard_and_add stack f =
    axiom stack (guard_axiom stack f)

let ground_terms stack =
  List.fold_left
    (fun acc f -> TermSet.union (ground_terms f) acc)
    TermSet.empty
    (get_form stack)


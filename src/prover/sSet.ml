open Form
(* predicates/axioms for the Stratified Set part of GRASS *)

(* copy-pasted part used in the currend/old translation.
 * rather than using axioms we shoud introduce predicates/operations.
 *)

let mem set v = mk_pred set [v]

let included set1 set2 =
  mk_implies (mem set1 Axioms.var1) (mem set2 Axioms.var1)

let equiv set1 set2 =
  mk_equiv (mem set1 Axioms.var1) (mem set2 Axioms.var1)

let disjoint set1 set2 =
  mk_or [Form.mk_not (mem set1 Axioms.var1); mk_not (mem set2 Axioms.var1)]

let union u set1 set2 =
  mk_equiv (mem u Axioms.var1) (mk_or [(mem set1 Axioms.var1); (mem set2 Axioms.var1)])

let inter i set1 set2 =
  mk_equiv (mem i Axioms.var1) (mk_and [(mem set1 Axioms.var1); (mem set2 Axioms.var1)])

let difference diff set1 set2 =
  mk_equiv (mem diff Axioms.var1) (mk_and [(mem set1 Axioms.var1); mk_not (mem set2 Axioms.var1)])

(* TODO reify the set operations:
 * should we have a datastructure for predicates ?
 * -> id, arity, type, (un)apply methods
 * -> unify with definition from model ?
 * -> put some information about the axioms/interpretation into the definition ?
 *)

type pred_sig = ident * int (*arity*)

let apply psig args =
  assert(List.length args = snd psig);
  mk_pred (fst psig) args

let unapply psig f =
  match f with
  |  Pred (id, args) when id = (fst psig) && (List.length args = snd psig) -> Some args
  | _ -> None

let member = (mk_ident "in", 2)
let subset = (mk_ident "sub", 2)
let equal = (mk_ident "eq", 2)
let intersection = (mk_ident "inter", 3)
let empty = (mk_ident "empty", 1)
(*
let union = (mk_ident "union", 3)
let disjoint = (mk_ident "disjoint", 2)
*)




type pred_template = string(*prefix*) * int(*arity*)

let instantiate tmpl id =
  let pid = ((fst tmpl) ^ "_" ^ (fst id), snd id) in
    (pid, snd tmpl)

let is tmpl id = 
  let re = Str.regexp (fst tmpl) in
    Str.string_match re (fst id) 0

let fun_of tmpl id =
  let len = String.length (fst tmpl) in
    (String.sub (fst id) len (String.length (fst id) - len), (snd id))

let extract tmpl f = match f with
  | Pred (id, _) when is tmpl id -> Some (fun_of tmpl id)
  | _ -> None

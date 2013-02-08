open Util
open Form
open FormUtil
open InstGen

let open_axioms openCond axioms = 
  let open_axiom = function
  | Binder (b, vs, f, a) -> 
      Binder (b, List.filter (~~ (openCond f)) vs, f, a)
  | f -> f
  in List.map open_axiom axioms

let isFld f = function (_, Fld _) -> true | _ -> false

let isFunVar f =
  let fvars = vars_in_fun_terms f in
  fun v -> IdSrtSet.mem v fvars


(** Adds instantiated theory axioms for graph reachability to formula f
 ** assumes that f is typed *)
let reduce_reach fs =
  let gts = TermSet.add mk_null (ground_terms (mk_and fs)) in
  (* instantiate the variables of sort fld in all reachability axioms *)
  let basic_pt_flds = TermSet.filter (has_sort (Fld Loc) &&& is_free_const) gts in
  let reachwo_ax = open_axioms isFld (Axioms.reachwo_axioms ()) in
  let defs, reachwo_ax1 = instantiate_with_terms false fs reachwo_ax basic_pt_flds in
  (* generate local instances of all axioms in which variables occur below function symbols *)
  let defs2, reachwo_ax2 = instantiate_with_terms true fs (open_axioms isFunVar reachwo_ax1) gts in
  (* generate instances of all update axioms *)
  let write_ax = open_axioms isFunVar (Axioms.write_axioms ()) in
  let defs3, write_ax1 = instantiate_with_terms true fs write_ax gts in
  defs @ defs2 @ defs3 @ fs, write_ax1 @ reachwo_ax2


(** Reduces the given formula to the target theory fragment, as specified by the configuration *)
let reduce f = 
  let rec split_ands acc = function
    | BoolOp(And, fs) :: gs -> split_ands acc (fs @ gs)
    | f :: gs -> split_ands (f :: acc) gs
    | [] -> List.rev acc
  in
  let fs = split_ands [] [f] in
  let fs1, reach_axioms = reduce_reach fs in
  fs1 @ reach_axioms

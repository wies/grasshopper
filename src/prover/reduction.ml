open Util
open Form
open FormUtil
open InstGen

let open_axiom openCond = function
  | Binder (b, vs, f, a) -> 
      Binder (b, List.filter (neg (openCond f)) vs, f, a)
  | f -> f

let openFld f = function (_, Fld _) -> true | _ -> false

let openFunVars f =
  let fvars = vars_in_fun_terms f in
  fun v -> IdSrtSet.mem v fvars

let filter_terms_by_sort ts srt = TermSet.filter (fun t -> sort_of t = Some srt) ts

(** Adds instantiated theory axioms for graph reachability to formula f
 ** assumes that f is typed *)
let reduce_reach fs =
  let gts = ground_terms (mk_and fs) in
  (* instantiate the variables of sort fld in all reachability axioms *)
  let basic_pt_flds = filter_terms_by_sort gts (Fld Loc) in
  let reachwo_ax = List.map (open_axiom openFld) (Axioms.reachwo_axioms ()) in
  let defs, reachwo_ax1 = instantiate_with_terms false fs reachwo_ax basic_pt_flds in
  (* generate local instances of all axioms in which variables occur below function symbols *)
  let reachwo_ax2 = List.map (open_axiom openFunVars) reachwo_ax1 in
  let defs2, instances = instantiate_with_terms true fs reachwo_ax2 gts in
  defs @ defs2 @ fs, instances


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

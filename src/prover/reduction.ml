open Form
open FormUtil
open InstGen

(** Adds instantiated theory axioms for graph reachability to formula f
 ** assumes that f is typed *)
let reduce_reach fs =
  let gts = ground_terms (mk_and fs) in
  (* instantiate the variables of sort fld in all reachability axioms *)
  let open_axiom = function
    | Binder (b, vs, f, a) ->
	Binder (b, List.filter (function (_, Fld _) -> false | _ -> true) vs, f, a)
    | f -> f
  in
  let basic_pt_flds = 
    TermSet.filter 
      (function 
	| App (FreeSym _, _, Some (Fld Loc)) -> true 
	| _ -> false
      )
      gts
  in
  let reachwo_ax = List.map open_axiom (Axioms.reachwo_axioms ()) in
  let defs, reachwo_ax1 = instantiate_with_terms false fs reachwo_ax basic_pt_flds in
  (* generate local instances of all axioms in which variables occur below function symbols *)
  let open_axiom2 = function
    | Binder (b, vs, f, a) ->
	let fvars = vars_in_fun_terms f in
	let vs' = List.filter (fun v -> not (IdSrtSet.mem v fvars)) vs in
	Binder (b, vs', f, a)
    | f -> f
  in
  let reachwo_ax2 = List.map open_axiom2 reachwo_ax1 in
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

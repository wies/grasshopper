open Printf 
open Prog
open SymbState 
open Grass 
open GrassUtil
open Verifier
open Axioms 

let rec remove_at n = function
  | [] -> []
  | h :: t -> if n = 0 then t else h :: remove_at (n - 1) t

let sort_of_ret_val f = 
  match f with
  | Atom (App (Eq, [h1; h2], _), _) -> sort_of h2 
  | Atom (App (Plus, [h1; h2], _), _) -> sort_of h2 
  | Atom (App (Ite, [_; t1; _], _), _) -> sort_of t1
  | _ -> failwith "foo"

let subst_ret_val f sub = 
  match f with
  | Atom (App (Eq, [h1; h2], a), b) -> 
      Debug.debug(fun() -> "subs ret val\n");
      Atom (App (Eq, [sub; h2], a), b)  
  | Atom (App (Ite, ts, a), _) ->
      mk_eq sub (App (Ite, ts, a))
  | _ -> f

let get_ret_val f = 
  match f with
  | Atom (App (Eq, [h1; h2], _), _) -> h2 
  | Atom (App (Plus, [h1; h2], _) as a, _) -> a 
  | Atom (App (Ite, ts, x), y) -> App (Ite, ts, x)
  | _ -> failwith "foo"

let get_pc_stack (_, _, s) = s

let string_of_sorted_id idsrt =
  sprintf "(%s, %s)" (string_of_ident (fst idsrt)) (string_of_sort (snd idsrt))

let string_of_sorted_ids ids =
  ids 
  |> List.map (fun t -> string_of_sorted_id t)
  |> String.concat ", "
  |> sprintf "[%s]"

(* better to get precond from the state on the stack*)
let fun_axiom name args srt precond body state =
  Debug.debug(fun () -> sprintf "Generating function axiom for (%s) \n State:\n {%s\n}\n\n"
    (string_of_ident name) (string_of_state state));

  (* lookup each arg in args and get symbolic values *)
  let symb_args =
    List.map (fun a ->
      find_symb_val state.store a)
    args
  in

  (* replace rhs formula without the equality on the return val *)
  let rhs = body in

  Debug.debug(fun () -> sprintf "RHS (%s) \n" (string_of_form rhs));
  let rhs_srt = sort_of_ret_val rhs in

  (* use sorted_free_vars_term to get the snap vars*)
  let bound_vars =
    List.rev symb_args
  in
  let fv = sorted_free_vars_term (get_ret_val rhs) in
  let fvs =
    IdSrtSet.filter (fun id ->
      let re = Str.regexp "fresh_snap*" in
      Str.string_match re
      (string_of_ident (fst id)) 0) fv
  in
  let fvs = IdSrtSet.elements fvs in

  let bounds =
    List.rev (
      List.fold_left 
       (fun acc v ->
          match v with
          | Var (id, srt) -> (id, srt) :: acc
          | _ -> 
          acc) [] bound_vars)
  in
  let bounds = fvs @ bounds in

  (* Axioms need to have Var(id, srt) insead of App(FreeSym fresh_snap, [], ...)*)
  let sm = List.fold_right 
   (fun (id, srt) sm -> 
     IdMap.add id (Var (id, srt)) sm
   )
   bounds IdMap.empty
  in

  (* build the axiom *)
  let lhs_vars =
    List.map
      (fun (id, srt) ->
        Var(id, srt))
      bounds
  in
  let lhs = mk_free_fun rhs_srt name (List.rev lhs_vars) in  

  let precond_form =
    mk_and (pc_collect_constr state.pc)
  in

  let pred =
    (mk_implies precond_form (subst_ret_val rhs lhs))
  in
  Debug.debug(fun () -> sprintf "PRED (%s)\n" (string_of_form pred));
  let pred' = GrassUtil.subst_consts sm pred in

  let fun_axiom_id = mk_name_generator (string_of_ident name) in
  let name_str, _ = (fun_axiom_id rhs_srt) in

  let fun_axiom = mk_forall bounds pred' in
  let ax = mk_axiom name_str fun_axiom in
  let fun_match_term, generate_knowns = (lhs, []) in

  (* annotate the axiom with term generators *)
  let m = Match (mk_known fun_match_term, []) in
  annotate (add_match fun_match_term lhs_vars m 
    (add_generators state.prog (Some(name, m)) ax)) generate_knowns

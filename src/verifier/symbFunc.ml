open Printf 
open Prog
open SymbState 
open Grass 
open GrassUtil
open Axioms 

let rec remove_at n = function
  | [] -> []
  | h :: t -> if n = 0 then t else h :: remove_at (n - 1) t

let sort_of_ret_val f = 
  match f with
  | Atom (App (Eq, [h1; h2], _), _) -> sort_of h2 
  | Atom (App (Ite, [_; t1; _], _), _) -> sort_of t1
  | _ -> failwith "foo"


let subst_ret_val f sub = 
  match f with
  | Atom (App (Eq, [h1; h2], a), b) ->  Atom (App (Eq, [sub; h2], a), b)  
  | Atom (App (Ite, ts, a), _) ->
      mk_eq sub (App (Ite, ts, a))
  | _ -> f

let get_ret_val f = 
  match f with
  | Atom (App (Eq, [h1; h2], _), _) ->
      Debug.debug( fun () -> sprintf "GETRETVAL (%s)\n" (string_of_term h2));
      h2 
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

let fun_axiom name args srt precond state =
  Debug.debug(fun () -> sprintf "Generating function axiom for (%s) \n State:\n {%s\n}\n\n"
    (string_of_ident name) (string_of_state state));

  (* lookup each arg in args and get symbolic values *)
  let symb_args = List.map (fun a -> find_symb_val state.store a) args in
  Debug.debug(fun () -> sprintf "symb_args %s\n" (string_of_term_list symb_args));

  (* replace rhs formula without the equality on the return val *)
  let rhs = List.hd (remove_at 0 (get_pc_stack (List.hd state.pc))) in
  Debug.debug(fun () -> sprintf "rhs (%s)\n" (string_of_form rhs));
  let rhs_srt = sort_of_ret_val rhs in

  (* use sorted_free_vars_term to get the snap vars*)
  let bound_vars = List.rev symb_args in
  let fv = sorted_free_vars_term (get_ret_val rhs) in
  let fvs = IdSrtSet.filter (fun id ->
    let re = Str.regexp "fresh_snap*" in
    Str.string_match re (string_of_ident (fst id)) 0) fv in
  let fvs = IdSrtSet.elements fvs in


  let bounds = List.rev (List.fold_left (fun acc v ->
    match v with
    | Var (id, srt) -> (id, srt) :: acc
    | _ -> 
        acc
  ) [] bound_vars) in
  let bounds = fvs @ bounds in

  (* Axioms need to have Var(id, srt) insead of App(FreeSym fresh_snap, [], ...)*)
  let sm = List.fold_right 
   (fun (id, srt) sm -> 
     IdMap.add id (Var (id, srt)) sm
   )
   bounds IdMap.empty
  in
  let _ = List.iter (fun (id, srt) -> Printf.printf "*** AXIOM BOUNDS (%s, %s)\n" (string_of_ident id) (string_of_sort srt)) bounds in
  let _ = IdMap.iter (fun k v -> Printf.printf "*** AXIOM SM k, v (%s, %s)\n" (string_of_ident k) (string_of_term v)) sm in

  (* build the axiom *)
  let lhs_vars = List.map (fun (id, srt) -> Var(id, srt)) bounds in
  let lhs = mk_free_fun rhs_srt name (List.rev lhs_vars) in  
  Debug.debug(fun () -> sprintf "LHS (%s)\n" (string_of_term lhs));

  let pred = (mk_sequent precond [subst_ret_val rhs lhs]) in
  Debug.debug(fun () -> sprintf "PRED (%s)\n" (string_of_form pred));
  let pred' = GrassUtil.subst_consts sm pred in

  let fun_axiom_id = mk_name_generator (string_of_ident name) in
  let name, _ = (fun_axiom_id rhs_srt) in

  let fun_axiom = mk_forall bounds pred' in
  let _ = List.iter (fun (id, srt) -> Printf.printf "*** AXIOM BOUNDS 2 (%s, %s)\n" (string_of_ident id) (string_of_sort srt)) bounds in
  mk_axiom name fun_axiom

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
  | _ -> failwith "foo"

let subst_ret_val f sub = 
  match f with
  | Atom (App (Eq, [h1; h2], a), b) ->  Atom (App (Eq, [sub; h2], a), b)  
  | _ -> f 

let get_ret_val f = 
  match f with
  | Atom (App (Eq, [h1; h2], _), _) -> h2 
  | _ -> failwith "foo"

let get_pc_stack (_, _, s) = s

let string_of_sorted_id idsrt =
  sprintf "(%s, %s)" (string_of_ident (fst idsrt)) (string_of_sort (snd idsrt))

let string_of_sorted_ids ids =
  ids 
  |> List.map (fun t -> string_of_sorted_id t)
  |> String.concat ", "
  |> sprintf "[%s]"

let fun_axiom name args srt state =
  Debug.debug(fun () -> sprintf "Generating function axiom for (%s) \n State:\n {%s\n}\n\n"
    (string_of_ident name) (string_of_state state));

  (* replace rhs formula without the equality on the return val *)
  let rhs = List.hd (remove_at 0 (get_pc_stack (List.hd state.pc))) in
  let rhs_srt = sort_of_ret_val rhs in

  (* find the snap variables in the rhs signature *)
  let rhs_sig = sign_term (get_ret_val rhs) in
  let rhs_vars = SymbolMap.fold (fun k arity acc -> 
    if List.length (fst arity) = 0 then
      (mk_var (snd arity) (mk_ident (string_of_symbol k))) :: acc
    else
      acc
    ) rhs_sig []
  in

  let bound_vars = (List.rev args) @ rhs_vars in
  let bounds = List.rev (List.fold_left (fun acc v ->
    match v with
    | Var (id, srt) -> (id, srt) :: acc
    | _ -> acc
  ) [] bound_vars) in

  (* build the axiom *)
  let lhs = mk_free_fun rhs_srt name (List.rev args @ rhs_vars) in  
  let pred = subst_ret_val rhs lhs in

  let fun_axiom_id = mk_name_generator (string_of_ident name) in
  let name, _ = (fun_axiom_id rhs_srt) in

  let fun_axiom = mk_forall bounds pred in
  mk_axiom name fun_axiom

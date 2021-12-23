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

let rec subst_var f t =
  match f with
  | Atom (Var (_, _), a) -> Atom (t, a) 
  | Atom (t, a) -> Atom (t, a) 
  | BoolOp (op, fs) -> BoolOp(op, List.map (fun f -> subst_var f t) fs)
  | Binder (b, vs, f, a) -> Binder (b, vs, subst_var f t, a)

let sort_of_ret_val f = 
  match f with
  | Atom (App (Eq, [h1; h2], _), _) -> sort_of h2 
  | Atom (App (GtEq, [h1; h2], _), _) -> sort_of h2 
  | Atom (App (Plus, [h1; h2], _), _) -> sort_of h2 
  | Atom (App (Ite, [_; t1; _], _), _) -> sort_of t1
  | _ -> failwith "foo"

let subst_ret_val f sub = 
  match f with
  | Atom (App (op, [h1; h2], a), b) -> 
      Debug.debug(fun() -> "subs ret val\n");
      Atom (App (op, [sub; h2], a), b)  
  | Atom (App (Ite, ts, a), _) ->
      mk_eq sub (App (Ite, ts, a))
  | _ -> f

let subst_rhs_val f sub = 
  match f with
  | Atom (App (Eq, [h1; h2], a), b) -> 
      Debug.debug(fun() -> "subs ret val\n");
      Atom (App (Eq, [h1; sub], a), b)  
  | Atom (App (Ite, ts, a), _) ->
      mk_eq (App (Ite, ts, a)) sub
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

let gen_fun_axiom state state_precond name args return_val = 
  Debug.debug(fun () -> sprintf "Generating function axiom for (%s) \n State:\n {%s\n}\n\n"
    (string_of_ident name) (string_of_state state));

  let postcond_stack =
    match state.pc, state_precond.pc with
    | (_, _, post_hd) :: _, [] -> post_hd
    | (_, _, post_hd) :: _, (_, _, pre_hd) :: _ -> diff_stacks post_hd pre_hd
    | _ -> failwith "can't generate axiom for function with no pre/postcond" 
  in

  Debug.debug(fun () -> sprintf "Postcond stack (%s) \n" (string_of_forms postcond_stack));
  (* function postconditions are only pure formulas so we need to scrub
   * the formula of fresh_snap terms *)
  let stack' = 
    List.filter (fun f -> not (remove_snaps_2 f)) 
    postcond_stack 
  in
  let state = {state with 
      pc=((update_pc_stack state stack') :: (List.tl state.pc))}
  in

  Debug.debug(fun () -> sprintf "Stack after scrub (%s) \n" (string_of_pcset stack'));
  (* lookup each arg in args and get symbolic values *)
  let symb_args =
    List.map (fun a ->
      find_symb_val state.store a)
    args 
  in

  (* replace rhs formula without the equality on the return val *)
  let postcond_form = mk_and (get_pc_stack (List.hd state.pc))
  in

  (* To get the RHS we can peel off the stack until the tail is equal to the stack from precond *)
  (* remove fresh_snaps from the stack *)
  Debug.debug(fun () -> sprintf "PostCond form (%s) \n" (string_of_form postcond_form));
  
  let precond_form = mk_and (List.fold_left (fun acc (id, bc, pcs) -> pcs @ acc) [] state_precond.pc) in

  Debug.debug(fun () -> sprintf "Precond form (%s) \n" (string_of_form precond_form));
  let fv = sorted_free_vars postcond_form in
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
          acc) [] symb_args)
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
  let precond_vars =
    List.map
      (fun (id, srt) ->
        Var(id, srt))
      bounds
  in

  let lhs = mk_free_fun (sort_of return_val) name (List.rev precond_vars) in  

  (* The precondition is the second element in the stack *)

  let symb_ret_var = (find_symb_val state.store (id_of return_val)) in
  let sm' = IdMap.add (id_of symb_ret_var) lhs IdMap.empty in
  let f = mk_implies precond_form postcond_form in
  let f = subst sm' f in

  let pred' = GrassUtil.subst_consts sm f in
  let fun_axiom_id = mk_name_generator (string_of_ident name) in
  let name_str, _ = fun_axiom_id (sort_of return_val) in
  let fun_axiom = mk_forall bounds pred' in

  let ax = mk_axiom name_str fun_axiom in
  let fun_match_term, generate_knowns = (lhs, []) in

  (* annotate the axiom with term generators *)
  let m = Match (mk_known fun_match_term, []) in
  annotate (add_match fun_match_term precond_vars m 
    (add_generators state.prog (Some(name, m)) ax)) generate_knowns

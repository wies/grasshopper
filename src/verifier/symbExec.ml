(** {5 Symbolic execution based verifier} *)

open Util
open Grass
open GrassUtil
open Prog

exception NotYetImplemented
let todo () = raise NotYetImplemented


let string_of_id_term_map sm = (IdMap.fold (fun x t str -> str ^ (Printf.sprintf "  %s -> %s" (string_of_ident x) (string_of_term t))) sm "")


(** ----------- Symbolic state and manipulators ---------- *)

(** A symbolic state is a (pure formula, a list of spatial predicates) *)
type state = form * (Sl.pred_symbol * term list) list

let state_empty = (mk_true, [])

(** Convert a specification into a symbolic state. *)
let state_of_spec_list specs : state =
  let rec state_of_sl_form (pure, spatial) = function
    | Sl.Pure (f, _) -> state_of_form (pure, spatial) f
    | Sl.Atom (p, ts, _) -> pure, (p, ts) :: spatial
    | Sl.SepOp (Sl.SepStar, f1, f2, _) ->
      let pure, spatial = state_of_sl_form (pure, spatial) f2 in
      state_of_sl_form (pure, spatial) f1
    | Sl.SepOp (Sl.SepIncl, _, _, _) -> todo ()
    | Sl.SepOp (Sl.SepPlus, _, _, _) -> todo ()
    | Sl.BoolOp _ -> todo ()
    | Sl.Binder _ -> todo ()
    (* Note: if you allow binders, make substitutious capture avoiding! *)
  and state_of_form (pure, spatial) f =
    let f = filter_annotations (fun _ -> false) f in
    smk_and [f; pure], spatial
  in
  List.fold_left (fun state spec ->
      match spec.spec_form with
      | SL slform -> state_of_sl_form state slform
      | FOL form -> state_of_form state form
    ) state_empty specs

let string_of_state ((pure, spatial): state) =
  let spatial =
    match spatial with
    | [] -> "emp"
    | spatial ->
      spatial
      |> List.map (fun (p, ts) -> Sl.Atom (p, ts, None) |> Sl.string_of_form)
      |> String.concat " * "
  in
  Printf.sprintf "%s | %s" (string_of_form pure) spatial

(** Substitute all variables (constants) in state [(pure, spatial)] with terms 
  according to substitution map [sm].
  This operation is not capture avoiding. *)
let subst_state sm ((pure, spatial): state) : state =
  let spatial =
    List.map (fun (p, ts) -> (p, List.map (subst_consts_term sm) ts)) spatial
  in
  (subst_consts sm pure, spatial)


let print_state src_pos state =
  Debug.info (fun () ->
      Printf.sprintf "\nState at %s:\n  %s\n"
        (string_of_src_pos src_pos) (string_of_state state)
  )


(** ----------- Re-arrangement and normalization rules ---------- *)

let find_equalities (pure: form) =
  let rec find_eq sm = function
    | Atom (App (Eq, [t2; (App (FreeSym id, [],  _))], _), _)
    | Atom (App (Eq, [(App (FreeSym id, [],  _)); t2], _), _) ->
      (* TODO do some kind of normalization to avoid checking both cases *)
      IdMap.add id t2 sm
    | BoolOp (And, fs) ->
      List.fold_left find_eq sm fs
    | _ -> sm
  in
  find_eq IdMap.empty pure

let rec remove_trivial_equalities = function
  | Atom (App (Eq, [t1; t2], _), _) as f -> if t1 = t2 then mk_true else f
  | BoolOp (op, fs) -> smk_op op (List.map remove_trivial_equalities fs)
  | Binder (b, vs, f, anns) -> Binder (b, vs, remove_trivial_equalities f, anns)
  | f -> f


(** ----------- Lemmas for proving entailments ---------- *)

(** A lemma is of the form: pure /\ spatial |= pure /\ spatial *)
type lemma = form * (Sl.pred_symbol * term list) list * form * (Sl.pred_symbol * term list) list

let dummy_srt = FreeSrt ("TODO", 0)
let x = Var (("x", 0), dummy_srt)
let y = Var (("y", 0), dummy_srt)
let nil = mk_null dummy_srt
let lseg = ("lseg", 0)
let next = mk_free_const dummy_srt ("next", 0)

let unfolding_lemmas: lemma list = [
  (* x != nil /\ lseg(x, nil) |= x |-> y * lseg(y, nil) *)
  (mk_neq x nil, [(Sl.Pred lseg, [x; nil])], mk_eq (* TODO x.*)next y, [(Sl.Region, [x]); (Sl.Pred lseg, [y; nil])]);
]
(* TODO This is too painful. Extract from predicate instead.
  args can be forall vars, returns can be new existentials *)

(** ----------- Symbolic Execution ---------- *)

let check_entailment (p1, sp1) (p2, sp2) =
  Printf.printf "\n----Checking entailment:\n%s\n    |=\n%s\n" (string_of_state (p1, sp1)) (string_of_state (p2, sp2));

  (* Find equalities in LHS and substitute in RHS *)
  let eq_sm = find_equalities p1 in
  Printf.printf "\nFound equalities to substitute: %s\n" (string_of_id_term_map eq_sm);
  let (p1, sp1) = subst_state eq_sm (p1, sp1) in
  let (p2, sp2) = subst_state eq_sm (p2, sp2) in
  Printf.printf "\nNew RHS: %s\n" (string_of_state (p2, sp2));

  (* Remove trivial equalities *)
  let (p1, p2) = remove_trivial_equalities p1, remove_trivial_equalities p2 in

  match sp2 with
  | [] -> (* If RHS spatial is emp, then pure part must be true *)
    if p2 = mk_true then begin
      Printf.printf "RHS is true | emp.\n";
      [] end
    else
      (* TODO call SMT solver here? :) *)
      todo ()
  | _ -> todo ()


(** Symbolically execute command [comm] on state [state] and return final state. *)
let rec symb_exec state comm =
  print_state (source_pos comm) state;
  (* TODO get the type from the program somehow? *)
  let mk_var_term id = mk_free_const (FreeSrt ("TODO", 0)) id in
  match comm with
  | Basic (Assign {assign_lhs=ids; assign_rhs=ts}, _) ->
    (* TODO this is incorrect for field assignments! *)
    (* TODO simultaneous assignments can't touch heap, so do all at once *)
    List.combine ids ts
    |> List.fold_left (fun state (id, t) ->
        Printf.printf "--Assignment %s := %s\n" (string_of_ident id) (string_of_term t);
        let id' = fresh_ident (name id) in
        let sm = IdMap.singleton id (mk_var_term id') in
        print_endline (string_of_id_term_map sm);
        let t' = subst_consts_term sm t in
        Printf.printf "----Substituted id' = %s, t' = %s\n" (string_of_ident id') (string_of_term t');
        let (pure, spatial) = subst_state sm state in
        smk_and [(mk_eq (mk_var_term id) t'); pure], spatial
      ) state
  | Seq (comms, _) ->
    List.fold_left symb_exec state comms
  | _ -> todo ()


(** Check procedure [proc] in program [prog] using symbolic execution. *)
let check prog proc =
  Debug.info (fun () ->
      "Checking procedure " ^ string_of_ident (name_of_proc proc) ^ "...\n");

  match proc.proc_body with
  | Some comm ->
    let precond = state_of_spec_list proc.proc_contract.contr_precond in
    let postcond = state_of_spec_list proc.proc_contract.contr_postcond in
    let state = symb_exec precond comm in
    print_state (comm |> source_pos |> end_pos) state;
    check_entailment state postcond
  | None ->
    []

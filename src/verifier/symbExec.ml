(** {5 Symbolic execution based verifier} *)

open Util
open Grass
open GrassUtil
open Prog

exception NotYetImplemented


(** ----------- Symbolic state and manipulators ---------- *)

(** A symbolic state is a (pure formula, a list of spatial predicates) *)
type state = form * (Sl.pred_symbol * term list) list

let state_empty = (mk_true, [])

(** Convert a specification into a symbolic state. *)
let state_of_spec_list specs : state =
  let rec state_of_sl_form (pure, spatial) = function
    | Sl.Pure (f, _) -> smk_and [f; pure], spatial
    | Sl.Atom (p, ts, _) -> pure, (p, ts) :: spatial
    | Sl.SepOp (Sl.SepStar, f1, f2, _) ->
      let pure, spatial = state_of_sl_form (pure, spatial) f2 in
      state_of_sl_form (pure, spatial) f1
    | Sl.SepOp (Sl.SepIncl, _, _, _) -> raise NotYetImplemented
    | Sl.SepOp (Sl.SepPlus, _, _, _) -> raise NotYetImplemented
    | Sl.BoolOp _ -> raise NotYetImplemented
    | Sl.Binder _ -> raise NotYetImplemented
    (* Note: if you allow binders, make substitutious capture avoiding! *)
  in
  let state_of_form (pure, spatial) f = smk_and [f; pure], spatial in
  List.fold_left (fun state spec ->
      match spec.spec_form with
      | SL slform -> state_of_sl_form state slform
      | FOL form -> state_of_form state form
    ) state_empty specs

let string_of_state ((pure, spatial): state) =
  let spatial =
    List.fold_right (fun (p, ts) f -> Sl.SepOp (Sl.SepStar, Sl.Atom (p, ts, None), f, None))
      spatial (Sl.Pure (mk_true, None))
  in
  Sl.SepOp (Sl.SepStar, Sl.Pure (pure, None), spatial, None)
  |> Sl.string_of_form

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


(** ----------- Symbolic Execution ---------- *)

let check_entailment f1 f2 =
  raise NotYetImplemented


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
        print_endline (IdMap.fold (fun x t str -> str ^ (Printf.sprintf "  %s -> %s" (string_of_ident x) (string_of_term t))) sm "");
        let t' = subst_consts_term sm t in
        Printf.printf "----Substituted id' = %s, t' = %s\n" (string_of_ident id') (string_of_term t');
        let (pure, spatial) = subst_state sm state in
        smk_and [(mk_eq (mk_var_term id) t'); pure], spatial
      ) state
  | Seq (comms, _) ->
    List.fold_left symb_exec state comms
  | _ -> raise NotYetImplemented


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

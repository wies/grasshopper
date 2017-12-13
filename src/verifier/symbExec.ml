(** {5 Symbolic execution based verifier} *)

open Util
open Grass
open GrassUtil
open Prog

exception NotYetImplemented
let todo () = raise NotYetImplemented


let string_of_id_term_map sm = (IdMap.fold (fun x t str -> str ^ (Printf.sprintf "  %s -> %s" (string_of_ident x) (string_of_term t))) sm "")


(** ----------- Symbolic state and manipulators ---------- *)

type spatial_pred =
  | PointsTo of ident * (ident * term) list  (** x |-> [f1: E1, ..] *)
  | Pred of ident * term list

let string_of_spatial_pred = function
  | PointsTo (id, fs) ->
    Printf.sprintf "%s |-> (%s)" (string_of_ident id)
      (fs |> List.map (fun (id, t) -> (string_of_ident id) ^ ": " ^ (string_of_term t))
        |> String.concat ", ")
  | Pred (id, ts) ->
    Printf.sprintf "%s(%s)" (string_of_ident id)
      (ts |> List.map string_of_term |> String.concat ", ")


(** A symbolic state is a (pure formula, a list of spatial predicates) *)
type state = form * spatial_pred list

let state_empty = (mk_true, [])

(** Convert a specification into a symbolic state.
  This also moves field read terms from pure formula to points-to predicates.
*)
let state_of_spec_list specs : state =
  (** [reads] is a map: location -> field -> new var, for ever field read *)
  let rec state_of_sl_form (pure, spatial) reads = function
    | Sl.Pure (f, _) ->
      state_of_form (pure, spatial) reads f
    | Sl.Atom (Sl.Emp, ts, _) ->
      (pure, spatial), reads
    | Sl.Atom (Sl.Region, [(App (SetEnum, [App (FreeSym x, [], _)], _))], _) -> (* acc(x) *)
      (pure, PointsTo (x, []) :: spatial), reads
    | Sl.Atom (Sl.Region, ts, _) -> todo ()
    | Sl.Atom (Sl.Pred p, ts, _) ->
      (pure, Pred (p, ts) :: spatial), reads
    | Sl.SepOp (Sl.SepStar, f1, f2, _) ->
      let (pure, spatial), pts = state_of_sl_form (pure, spatial) reads f2 in
      state_of_sl_form (pure, spatial) pts f1
    | Sl.SepOp (Sl.SepIncl, _, _, _) -> todo ()
    | Sl.SepOp (Sl.SepPlus, _, _, _) -> todo ()
    | Sl.BoolOp _ -> todo ()
    | Sl.Binder _ -> todo ()
    (* Note: if you allow binders, make substitutions capture avoiding! *)
  and state_of_form (pure, spatial) reads f =
    let f = filter_annotations (fun _ -> false) f in
    (* TODO map and fold at same time? *)
    let rec find_reads reads = function
      | Var _ -> reads
      | App (Read, [App (FreeSym fld, [], _); App (FreeSym loc, [], _)], srt) ->
        if (IdMap.mem loc reads |> not) then
          IdMap.add loc (IdMap.singleton fld (mk_fresh_var srt "v")) reads
        else if (IdMap.mem fld (IdMap.find loc reads) |> not) then
          IdMap.add loc (IdMap.add fld (mk_fresh_var srt "v") (IdMap.find loc reads)) reads
        else reads
      | App (Read, _, _) as t ->
        failwith @@ "Unmatched read term " ^ (string_of_term t)
      | App (_, ts, _) -> List.fold_left find_reads reads ts
    in
    let rec subst_reads reads = function
      | Var _ as t -> t
      | App (Read, [App (FreeSym fld, [], _); App (FreeSym loc, [], _)], srt) ->
        IdMap.find fld (IdMap.find loc reads)
      | App (sym, ts, srt) -> App (sym, List.map (subst_reads reads) ts, srt)
    in
    let reads = fold_terms find_reads reads f in
    let f = map_terms (subst_reads reads) f in
    (smk_and [f; pure], spatial), reads
  in
  (* Convert all the specs into a state *)
  let (pure, spatial), reads =
    List.fold_left (fun (state, pts) spec ->
        match spec.spec_form with
        | SL slform -> state_of_sl_form state pts slform
        | FOL form -> state_of_form state pts form
      ) (state_empty, IdMap.empty) specs
  in
  (* Put collected read terms from pure part into spatial part *)
  let spatial =
    List.map (function
        | PointsTo (x, fs) ->
          let fs' = try IdMap.find x reads |> IdMap.bindings with Not_found -> [] in
          PointsTo (x, fs @ fs')
        | Pred _ as p -> p
      )
      spatial
  in
  (* If we have a points-to info without a corresponding acc(), fail *)
  let acc_ids = List.fold_left (fun s p ->
    match p with
    | PointsTo (x, _) -> IdSet.add x s
    | _ -> s) IdSet.empty spatial
  in
  if IdMap.exists (fun id _ -> IdSet.mem id acc_ids |> not) reads then
    failwith "state_of_spec_list: couldn't find corresponding acc"
  else
    (pure, spatial)

let string_of_spatial_pred = function
  | PointsTo (id, fs) ->
    Printf.sprintf "%s |-> (%s)" (string_of_ident id)
      (fs |> List.map (fun (id, t) -> (string_of_ident id) ^ ": " ^ (string_of_term t))
        |> String.concat ", ")
  | Pred (id, ts) ->
    Printf.sprintf "%s(%s)" (string_of_ident id)
      (ts |> List.map string_of_term |> String.concat ", ")

let string_of_state ((pure, spatial): state) =
  let spatial =
    match spatial with
    | [] -> "emp"
    | spatial -> spatial |> List.map string_of_spatial_pred |> String.concat " * "
  in
  Printf.sprintf "%s : %s" (string_of_form pure) spatial

let subst_spatial_pred sm = function
  | PointsTo (id, fs) ->
    PointsTo (id, List.map (fun (id, t) -> id, subst_consts_term sm t) fs)
  | Pred (id, ts) ->
    Pred (id, List.map (subst_consts_term sm) ts)

(** Substitute all variables (encoded as constants) in state [(pure, spatial)] with terms 
  according to substitution map [sm].
  This operation is not capture avoiding. *)
let subst_state sm ((pure, spatial): state) : state =
  (subst_consts sm pure, List.map (subst_spatial_pred sm) spatial)


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
      (* TODO don't add equalities with field read terms! *)
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

(** A lemma is of the form: pure /\ spatial |= pure /\ spatial.
  Universals are represented as Var terms, and existentials as FreeSymb consts.
*)
type lemma = state * state


(** Extract all lemmas (procedures named "lemma_*") from a program.
  procedure (x1, .. xN) returns (y1, .. yM)
    requires phi
    ensures psi
  is the lemma: forall x1, .. xN. phi |= exists y1, .. yM psi *)
let extract_lemmas prog : lemma list =
  let try_add_lemma ls proc =
    if Str.string_match (Str.regexp "lemma_*") (proc |> name_of_proc |> fst) 0
    then begin
      let lhs = state_of_spec_list proc.proc_contract.contr_precond in
      let rhs = state_of_spec_list proc.proc_contract.contr_postcond in
      (* Take formals (x1, .. xN) and create substitution map to make them vars *)
      let universals_sm =
        let dummy_srt = (FreeSrt ("TODO", 0)) in  (* TODO need to find actual sort? *)
        List.fold_left (fun sm id -> IdMap.add id (mk_var dummy_srt id) sm)
          IdMap.empty
          proc.proc_contract.contr_formals
      in
      Printf.printf "\n----Universals in lemma %s:%s\n" (proc |> name_of_proc |> fst) (string_of_id_term_map universals_sm);
      let lhs = subst_state universals_sm lhs in
      let rhs = subst_state universals_sm rhs in
      (lhs, rhs) :: ls
    end else ls
  in
  fold_procs try_add_lemma [] prog


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
  (* TODO get the type from the program somehow? *)
  let mk_var_term id = mk_free_const (FreeSrt ("TODO", 0)) id in
  match comm with
  | Basic (Assign {assign_lhs=ids; assign_rhs=ts}, _) ->
    (* TODO this is incorrect for field assignments! *)
    (* TODO simultaneous assignments can't touch heap, so do all at once *)
    List.combine ids ts
    |> List.fold_left (fun state (id, t) ->
        Printf.printf "\nExecuting assignment: %s := %s;\n" (string_of_ident id) (string_of_term t);
        let id' = fresh_ident (name id) in
        let sm = IdMap.singleton id (mk_var_term id') in
        let t' = subst_consts_term sm t in
        let (pure, spatial) = subst_state sm state in
        print_state (source_pos comm) state;
        smk_and [(mk_eq (mk_var_term id) t'); pure], spatial
      ) state
  | Seq (comms, _) ->
    List.fold_left symb_exec state comms
  | _ -> todo ()


(** Check procedure [proc] in program [prog] using symbolic execution. *)
let check prog proc =
  Debug.info (fun () ->
      "Checking procedure " ^ string_of_ident (name_of_proc proc) ^ "...\n");

  let _ = extract_lemmas prog in

  match proc.proc_body with
  | Some comm ->
    let precond = state_of_spec_list proc.proc_contract.contr_precond in
    let postcond = state_of_spec_list proc.proc_contract.contr_postcond in
    print_state (comm |> source_pos |> start_pos) precond;
    let state = symb_exec precond comm in
    print_state (comm |> source_pos |> end_pos) state;
    check_entailment state postcond
  | None ->
    []

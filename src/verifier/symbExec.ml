(** {5 Symbolic execution based verifier} *)

open Util
open Grass
open GrassUtil
open Prog
open Printf

exception NotYetImplemented
let todo () = raise NotYetImplemented


(** ----------- Symbolic state and manipulators ---------- *)

type spatial_pred =
  | PointsTo of term * (ident * term) list  (** x |-> [f1: E1, ..] *)
  | Pred of ident * term list

(** A symbolic state is a (pure formula, a list of spatial predicates).
  Note: program vars are represented as FreeSymb constants,
  existential vars are represented as Var variables.
 *)
type state = form * spatial_pred list

(** Equalities derived so far in the symbolic execution, as a map: ident -> term,
  kept so that they can be substituted into the command and the post. *)
type equalities = term IdMap.t


let empty_state = (mk_true, [])

let empty_eqs = IdMap.empty


let string_of_spatial_pred = function
  | PointsTo (x, fs) ->
    sprintf "%s |-> (%s)" (string_of_term x)
      (fs |> List.map (fun (id, t) -> (string_of_ident id) ^ ": " ^ (string_of_term t))
        |> String.concat ", ")
  | Pred (id, ts) ->
    sprintf "%s(%s)" (string_of_ident id)
      (ts |> List.map string_of_term |> String.concat ", ")

let string_of_state ((pure, spatial): state) =
  let spatial =
    match spatial with
    | [] -> "emp"
    | spatial -> spatial |> List.map string_of_spatial_pred |> String.concat " * "
  in
  sprintf "%s : %s" (string_of_form pure) spatial

let print_state src_pos eqs state =
  let eqs_str = IdMap.bindings eqs
    |> List.map (fun (x, t) -> (string_of_ident x) ^ " == " ^ (string_of_term t))
    |> String.concat " && "
  in
  Debug.info (fun () ->
      sprintf "\nState at %s:\n  %s : %s\n"
        (string_of_src_pos src_pos) eqs_str (string_of_state state)
  )

let string_of_equalities eqs =
  IdMap.bindings eqs
  |> List.map (fun (x, t) -> (string_of_ident x) ^ ": " ^ (string_of_term t))
  |> String.concat ", "
  |> sprintf "{%s}"


(** Convert a specification into a symbolic state.
  This also moves field read terms from pure formula to points-to predicates.
*)
let state_of_spec_list specs : state =
  (** [reads] is a map: location -> field -> new var, for every field read
    Sorry for using refs, but didn't know how to map and fold terms simultaneously
  *)
  let reads = ref TermMap.empty in
  let rec convert_term = function
    | Var _ as t -> t
    | App (Read, [App (FreeSym fld, [], _); loc], srt) -> (* loc.fld *)
      let loc = convert_term loc in
      if (TermMap.mem loc !reads |> not) then begin
        let new_var = (mk_fresh_var srt "v") in
        reads := TermMap.add loc (IdMap.singleton fld new_var) !reads;
        new_var
      end
      else if (IdMap.mem fld (TermMap.find loc !reads) |> not) then begin
        let new_var = (mk_fresh_var srt "v") in
        let flds_of_loc = IdMap.add fld (mk_fresh_var srt "v") (TermMap.find loc !reads) in
        reads := TermMap.add loc flds_of_loc !reads;
        new_var
      end else IdMap.find fld (TermMap.find loc !reads)
    | App (Read, _, _) as t ->
      failwith @@ "Unmatched read term " ^ (string_of_term t)
    | App (s, ts, srt) -> App (s, List.map convert_term ts, srt)
  in
  let convert_form (pure, spatial) f =
    let f = filter_annotations (fun _ -> false) f in
    let f = map_terms convert_term f in
    (smk_and [f; pure], spatial)
  in
  let rec convert_sl_form (pure, spatial) f =
    let fail () = failwith @@ "Unsupported formula " ^ (Sl.string_of_form f) in
    match f with
    | Sl.Pure (f, _) ->
      convert_form (pure, spatial) f
    | Sl.Atom (Sl.Emp, ts, _) ->
      (pure, spatial)
    | Sl.Atom (Sl.Region, [(App (SetEnum, [x], _))], _) -> (* acc(x) *)
      let x = convert_term x in
      (pure, PointsTo (x, []) :: spatial)
    | Sl.Atom (Sl.Region, ts, _) -> fail ()
    | Sl.Atom (Sl.Pred p, ts, _) ->
      (pure, Pred (p, ts) :: spatial)
    | Sl.SepOp (Sl.SepStar, f1, f2, _) ->
      let (pure, spatial) = convert_sl_form (pure, spatial) f2 in
      convert_sl_form (pure, spatial) f1
    | Sl.SepOp (Sl.SepIncl, _, _, _) -> fail ()
    | Sl.SepOp (Sl.SepPlus, _, _, _) -> fail ()
    | Sl.BoolOp _ -> fail ()
    | Sl.Binder _ -> fail ()
    (* Note: if you allow binders, make substitutions capture avoiding! *)
  in
  (* Convert all the specs into a state *)
  let (pure, spatial) =
    List.fold_left (fun state spec ->
        match spec.spec_form with
        | SL slform -> convert_sl_form state slform
        | FOL form -> convert_form state form
      ) empty_state specs
  in
  let reads = !reads in
  (* Put collected read terms from pure part into spatial part *)
  let spatial =
    List.map (function
        | PointsTo (x, fs) ->
          let fs' =
            try TermMap.find x reads |> IdMap.bindings with Not_found -> []
          in
          PointsTo (x, fs @ fs')
        | Pred _ as p -> p
      )
      spatial
  in
  (* TODO check the following in presence of x.next.next etc *)
  (* If we have a points-to info without a corresponding acc(), fail *)
  let alloc_terms = List.fold_left (fun s p ->
    match p with
    | PointsTo (x, _) -> TermSet.add x s
    | _ -> s) TermSet.empty spatial
  in
  if TermMap.exists (fun t _ -> TermSet.mem t alloc_terms |> not) reads then
    failwith "state_of_spec_list: couldn't find corresponding acc"
  else
    (pure, spatial)


let subst_term sm = subst_consts_term sm >> subst_term sm

let subst_spatial_pred sm = function
  | PointsTo (id, fs) ->
    PointsTo (id, List.map (fun (id, t) -> id, subst_term sm t) fs)
  | Pred (id, ts) ->
    Pred (id, List.map (subst_term sm) ts)

(** Substitute all variables (Vars and constants) in derived equalities [eqs],
  according to substitution [sm] *)
let subst_eqs eqs sm =
  IdMap.map (subst_term sm) eqs

(** Substitute all variables (encoded as constants) in state [(pure, spatial)] with terms 
  according to substitution map [sm].
  This operation is not capture avoiding. *)
let subst_state sm ((pure, spatial): state) : state =
  (* TODO also substitute vars *)
  (subst_consts sm pure, List.map (subst_spatial_pred sm) spatial)


(** ----------- Re-arrangement and normalization rules ---------- *)

let find_equalities eqs (pure: form) =
  let rec find_eq sm = function
    | Atom (App (Eq, [t2; (App (FreeSym id, [],  _))], _), _)
    | Atom (App (Eq, [(App (FreeSym id, [],  _)); t2], _), _) ->
      (* TODO also gather Var equalities *)
      (* TODO do some kind of normalization to avoid checking both cases *)
      IdMap.add id t2 sm
    | BoolOp (And, fs) ->
      List.fold_left find_eq sm fs
    | _ -> sm
  in
  find_eq eqs pure

let rec remove_trivial_equalities = function
  | Atom (App (Eq, [t1; t2], _), _) as f -> if t1 = t2 then mk_true else f
  | BoolOp (op, fs) -> smk_op op (List.map remove_trivial_equalities fs)
  | Binder (b, vs, f, anns) -> Binder (b, vs, remove_trivial_equalities f, anns)
  | f -> f

let apply_equalities eqs state =
  let (pure, spatial) = subst_state eqs state in
  remove_trivial_equalities pure, spatial

let simplify eqs ((pure, spatial): state) =
  let eqs = find_equalities eqs pure in
  eqs, apply_equalities eqs (pure, spatial)

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
      printf "\n----Universals in lemma %s:%s\n" (proc |> name_of_proc |> fst) (string_of_equalities universals_sm);
      let lhs = subst_state universals_sm lhs in
      let rhs = subst_state universals_sm rhs in
      (lhs, rhs) :: ls
    end else ls
  in
  fold_procs try_add_lemma [] prog


(** ----------- Symbolic Execution ---------- *)

let check_entailment eqs (p1, sp1) (p2, sp2) =
  Debug.info (fun () ->
    sprintf "\nChecking entailment, with eqs: %s\n" (string_of_equalities eqs)
  );
  let eqs, (p1, sp1) = simplify eqs (p1, sp1) in
  let (p2, sp2) = apply_equalities eqs (p2, sp2) in
  printf "%s\n    |=\n%s\n"
    (string_of_state (p1, sp1)) (string_of_state (p2, sp2));

  match sp2 with
  | [] -> (* If RHS spatial is emp, then pure part must be true *)
    if p2 = mk_true then begin
      printf "RHS is true | emp.\n";
      [] end
    else
      (* TODO call SMT solver here? :) *)
      todo ()
  | _ -> todo ()


(** Symbolically execute command [comm] on state [state] and return final state. *)
let rec symb_exec (eqs, state) comm =
  (* First, simplify the pre state *)
  let eqs, state = simplify eqs state in
  print_state (source_pos comm) eqs state;
  (* TODO get the type from the program *)
  let mk_var_term id = mk_free_const (FreeSrt ("TODO", 0)) id in
  match comm with
  | Basic (Assign {assign_lhs=[x];
      assign_rhs=[App (Read, [App (FreeSym fld, [], _); App (FreeSym _, [], _) as loc], srt)]}, _) ->
    Debug.info (fun () ->
      sprintf "\nExecuting lookup: %s := %s.%s;\n" (string_of_ident x)
        (string_of_term loc) (string_of_ident fld)
    );

    let loc = subst_term eqs loc in
    (** Returns [(fs, spatial')] s.t. [spatial] = [loc] |-> [fs] :: [spatial'] *)
    let find_ptsto loc spatial =
      let sp1, sp2 =
        List.partition (function | PointsTo (x, fs) -> x = loc | Pred _ -> false) spatial
      in
      match sp1 with
      | [PointsTo (_, fs)] -> Some (fs, sp2)
      | [] -> None
      | _ ->
        failwith @@ "find_ptsto was confused by " ^
          (sp1 |> List.map string_of_spatial_pred |> String.concat " &*& ")
    in
    (match find_ptsto loc (snd state) with
    | Some (fs, spatial') ->
      (* lookup fld in fs. now loc |-> fs' and (fld, e) is in fs' *)
      let e, fs' =
        try List.assoc fld fs, fs
        with Not_found -> let e = mk_fresh_var srt "v" in e, (fld, e) :: fs
      in
      let spatial' = PointsTo (loc, fs') :: spatial' in
      let x' = fresh_ident (name x) in
      let sm = IdMap.singleton x (mk_var_term x') in
      let e = subst_term sm e in
      let state = subst_state sm (fst state, spatial') in
      let eqs = IdMap.add x e (subst_eqs eqs sm) in
      eqs, state
    | None -> failwith @@ "Invalid lookup: " ^ (comm |> source_pos |> string_of_src_pos)
    )
  | Basic (Assign {assign_lhs=ids; assign_rhs=ts}, _) ->
    (* TODO simultaneous assignments can't touch heap, so do all at once *)
    List.combine ids ts
    |> List.fold_left (fun (eqs, state) (id, t) ->
        printf "\nExecuting assignment: %s := %s;\n" (string_of_ident id) (string_of_term t);
        let id' = fresh_ident (name id) in
        let sm = IdMap.singleton id (mk_var_term id') in
        let t' = subst_term sm t in
        let (pure, spatial) = subst_state sm state in
        let eqs = IdMap.add id t' (subst_eqs eqs sm) in
        eqs, (pure, spatial)
      ) (eqs, state)
  | Seq (comms, _) ->
    List.fold_left symb_exec (eqs, state) comms
  | _ -> todo ()


(** Check procedure [proc] in program [prog] using symbolic execution. *)
let check prog proc =
  Debug.info (fun () ->
      "Checking procedure " ^ string_of_ident (name_of_proc proc) ^ "...\n");

  match proc.proc_body with
  | Some comm ->
    let precond = state_of_spec_list proc.proc_contract.contr_precond in
    let postcond = state_of_spec_list proc.proc_contract.contr_postcond in
    Debug.info (fun () ->
      sprintf "  Precondition: %s\n  Postcondition: %s\n"
        (string_of_state precond) (string_of_state postcond)
    );

    let eqs = empty_eqs in
    let eqs, state = symb_exec (eqs, precond) comm in
    print_state (comm |> source_pos |> end_pos) eqs state;
    check_entailment eqs state postcond
  | None ->
    []

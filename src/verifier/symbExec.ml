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
  kept so that they can be substituted into the command and the post.
  Invariant: if map is {x1: E1, ...} then xi are distinct and xi is not in Ej for i != j.
  ASSUMES: vars and constants do not share names!
  *)
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
  let pure = (string_of_form pure |> String.map (function | '\n' -> ' ' | c -> c)) in
  sprintf "%s : %s" pure spatial

let string_of_equalities eqs =
  IdMap.bindings eqs
  |> List.map (fun (x, t) -> (string_of_ident x) ^ " = " ^ (string_of_term t))
  |> String.concat ", "
  |> sprintf "{%s}"

let print_state src_pos eqs state =
  Debug.info (fun () ->
      sprintf "\nState at %s:\n  %s : %s\n"
        (string_of_src_pos src_pos) (string_of_equalities eqs) (string_of_state state)
  )


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


(** Substitute both vars and constants in a term according to [sm]. *)
let subst_term sm = subst_consts_term sm >> subst_term sm

(** Substitute both vars and constants in a form according to [sm]. *)
let subst_form sm = subst_consts sm >> subst sm

let subst_spatial_pred sm = function
  | PointsTo (id, fs) ->
    PointsTo (subst_term sm id, List.map (fun (id, t) -> id, subst_term sm t) fs)
  | Pred (id, ts) ->
    Pred (id, List.map (subst_term sm) ts)

(** Substitute all (Vars and constants) in derived equalities [eqs],
  according to substitution [sm]
  TODO check this preserves equalities invariant! *)
let subst_eqs sm eqs =
  eqs |> IdMap.bindings
  |> List.fold_left (fun eqs (id, t) -> 
    let t' = subst_term sm t in
    match IdMap.find_opt id sm with
    | Some (Var (id', _))
    | Some (App (FreeSym id', _, _)) -> IdMap.add id' t' eqs
    | None -> IdMap.add id t' eqs
    | _ -> failwith "huh?"
  ) IdMap.empty

(** Substitute all variables and constants in state [(pure, spatial)] with terms 
  according to substitution map [sm].
  This operation is not capture avoiding. *)
let subst_state sm ((pure, spatial): state) : state =
  (subst_form sm pure, List.map (subst_spatial_pred sm) spatial)


(** Given two lists of idents and terms, create an equalities/subst map out of them. *)
let mk_eqs ids terms =
  List.combine ids terms
  |> List.fold_left (fun eqs (id, t) -> IdMap.add id t eqs) empty_eqs

(** Add [id] = [t] to equalities [eqs] while preserving invariant. *)
let add_eq id t eqs =
  (* Apply current substitutions to t *)
  let t = subst_term eqs t in
  (* Make sure things are not added twice *)
  if IdMap.mem id eqs then
    failwith @@ sprintf "Tried to add %s twice to eqs %s"
        (string_of_ident id) (string_of_equalities eqs)
  else
    let eqs = subst_eqs (IdMap.singleton id t) eqs in
    IdMap.add id t eqs


(** ----------- Re-arrangement and normalization rules ---------- *)

(** Find equalities of the form const == exp in [pure] and add to [eqs] *)
let find_equalities eqs (pure: form) =
  let rec find_eq sm = function
    | Atom (App (Eq, [(App (FreeSym id, [],  _)); t2], _), _)
    | Atom (App (Eq, [t2; (App (FreeSym id, [],  _))], _), _) ->
      add_eq id t2 sm
    | BoolOp (And, fs) ->
      List.fold_left find_eq sm fs
    | _ -> sm
  in
  find_eq eqs pure

(** Find equalities of the form var == exp in [pure] and return id -> exp map. *)
let find_var_equalities (pure: form) =
  let rec find_eq sm = function
    | Atom (App (Eq, [Var (id, _); t2], _), _)
    | Atom (App (Eq, [t2; Var (id, _)], _), _) ->
      add_eq id t2 sm
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

let apply_equalities eqs state =
  let (pure, spatial) = subst_state eqs state in
  remove_trivial_equalities pure, spatial

let remove_useless_existentials ((pure, spatial) as state : state) : state =
  (* Note: can also use GrassUtil.foralls_to_exists for this *)
  apply_equalities (find_var_equalities pure) state

(** Kill useless existential vars in [state], find equalities between constants,
  add to [eqs] and simplify. *)
let simplify eqs state =
  let (pure, spatial) = remove_useless_existentials state in
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

let check_pure_entail p1 p2 =
  if p1 = p2 || p2 = mk_true then true
  else (* TODO call SMT solver here? :) *)
    failwith @@ sprintf "Could not prove %s" (string_of_form p2)


(** Find a frame for state1 * fr |= state2, and an instantiation for TODO? *)
let rec find_frame ?(inst=empty_eqs) eqs (p1, sp1) (p2, sp2) =
  Debug.info (fun () ->
    sprintf "\n  Finding frame with %s for:\n    %s : %s &*& ??\n    |= %s\n" 
      (string_of_equalities inst) (string_of_equalities eqs)
      (string_of_state (p1, sp1)) (string_of_state (p2, sp2))
  );
  let fail () =
    failwith @@ sprintf "Could not find frame for entailment:\n%s\n|=\n%s\n"
      (string_of_state (p1, sp1)) (string_of_state (p2, sp2))
  in
  match sp2 with
  | [] ->
    (* Check if p2 is implied by p1 *)
    if check_pure_entail p1 p2 then
      sp1, inst
    else fail ()
  | PointsTo (x, fs2) :: sp2' ->
    (match find_ptsto x sp1 with
    | Some (fs1, sp1') ->
      let match_up_fields inst fs1 fs2 =
        let fs1, fs2 = List.sort compare fs1, List.sort compare fs2 in
        let rec match_up inst = function
        | (_, []) -> inst
        | ([], (f, e)::fs2') ->
          (* f not in LHS, so only okay if e is an ex. var not appearing anywhere else *)
          (* So create new const c, add e -> c to inst, and sub fs2' with inst *)
          todo ()
        | (fe1 :: fs1', fe2 :: fs2') when fe1 = fe2 -> match_up inst (fs1', fs2')
        | ((f1, e1) :: fs1', (f2, e2) :: fs2') when f1 = f2 ->
          (* e1 != e2, so only okay if e2 is ex. var *)
          (* add e2 -> e1 to inst and sub in fs2' to make sure e2 has uniform value *)
          (match e2 with
          | Var (e2_id, _) ->
            let sm = IdMap.singleton e2_id e1 in
            let fs2' = List.map (fun (f, e) -> (f, subst_term sm e)) fs2' in
            match_up (IdMap.add e2_id e1 inst) (fs1', fs2')
          | _ -> fail ()
          )
        | ((f1, e1) :: fs1', (f2, e2) :: fs2') when f1 <> f2 ->
          (* RHS doesn't need to have all fields, so drop (f1, e1) *)
          match_up inst (fs1', (f2, e2) :: fs2')
        | _ -> (* should be unreachable? *) assert false
        in
        match_up inst (fs1, fs2)
      in
      let inst = match_up_fields inst fs1 fs2 in
      let p2', sp2'' = subst_state inst (p2, sp2') in
      find_frame ~inst:inst eqs (p1, sp1') (p2', sp2'')
    | None -> fail ()
    )
  | pred :: sp2' when List.exists ((=) pred) sp1 -> (* match and remove equal preds *)
    let sp1a, sp1b = List.partition ((=) pred) sp1 in
    (match sp1a with
    | [pred'] -> find_frame ~inst:inst eqs (p1, sp1b) (p2, sp2')
    | _ -> fail ())
  | _ ->
    todo ()


let check_entailment eqs (p1, sp1) (p2, sp2) =
  Debug.info (fun () ->
    sprintf "\nChecking entailment:\n  %s : %s\n  |=\n  %s\n" (string_of_equalities eqs)
      (string_of_state (p1, sp1)) (string_of_state (p2, sp2))
  );
  let eqs, (p1, sp1) = simplify eqs (p1, sp1) in
  let (p2, sp2) = apply_equalities eqs (p2, sp2) |> remove_useless_existentials in
  Debug.info (fun () ->
    sprintf "\n  After equality reasoning:\n  %s : %s\n  |=\n  %s\n" (string_of_equalities eqs)
      (string_of_state (p1, sp1)) (string_of_state (p2, sp2))
  );

  (* Check if find_frame returns empt *)
  let fr, inst = find_frame eqs (p1, sp1) (p2, sp2) in
  match fr with
  | [] -> []
  | _ -> failwith @@ sprintf "Frame was not empty: %s" (string_of_state (mk_true, fr))


(** Symbolically execute command [comm] on state [state] and return final state. *)
let rec symb_exec prog proc (eqs, state) comm =
  (* First, simplify the pre state *)
  let eqs, state = simplify eqs state in
  print_state (source_pos comm) eqs state;

  let lookup_type id = (find_local_var proc id).var_sort in
  let mk_var_like id =
    let id' = fresh_ident (name id) in
    mk_var (lookup_type id) id'
  in
  let mk_const_term id = mk_free_const (lookup_type id) id in
  match comm with
  | Basic (Assign {assign_lhs=[x]; assign_rhs=[App (Read, [App (FreeSym fld, [], _);
      App (FreeSym _, [], _) as loc], srt)]}, _) ->
    Debug.info (fun () ->
      sprintf "\nExecuting lookup: %s := %s.%s;\n" (string_of_ident x)
        (string_of_term loc) (string_of_ident fld)
    );
    let loc = subst_term eqs loc in
    (match find_ptsto loc (snd state) with
    | Some (fs, spatial') ->
      (* lookup fld in fs. now loc |-> fs' and (fld, e) is in fs' *)
      let e, fs' =
        try List.assoc fld fs, fs
        with Not_found -> let e = mk_fresh_var srt "v" in e, (fld, e) :: fs
      in
      let spatial' = PointsTo (loc, fs') :: spatial' in
      let sm = IdMap.singleton x (mk_var_like x) in
      let e = subst_term sm e in
      let state = subst_state sm (fst state, spatial') in
      let eqs = add_eq x e (subst_eqs sm eqs) in
      eqs, state
    | None -> failwith @@ "Invalid lookup: " ^ (comm |> source_pos |> string_of_src_pos)
    )
  | Basic (Assign {assign_lhs=[fld]; assign_rhs=[App (Write, [App (FreeSym fld', [], _); 
      App (FreeSym _, [], _) as loc; rhs], srt)]}, _) when fld = fld' ->
    Debug.info (fun () ->
      sprintf "\nExecuting mutate: %s.%s := %s;\n" (string_of_term loc)
        (string_of_ident fld) (string_of_term rhs)
    );
    let (pure, spatial) = state in
    (* First, substitute eqs on loc and rhs *)
    let loc = subst_term eqs loc and rhs = subst_term eqs rhs in
    (match find_ptsto loc spatial with
    | Some (fs, spatial') ->
      (* mutate fs to fs' so that it contains (fld, rhs) *)
      let fs' =
        if List.exists (fst >> (=) fld) fs
        then List.map (fun (f, e) -> (f, if f = fld then rhs else e)) fs
        else (fld, rhs) :: fs
      in
      eqs, (pure, PointsTo (loc, fs') :: spatial')
    | None -> failwith @@ "Invalid write: " ^ (comm |> source_pos |> string_of_src_pos)
    )
  | Basic (Assign {assign_lhs=ids; assign_rhs=ts}, _) ->
    (* TODO simultaneous assignments can't touch heap, so do all at once *)
    (* TODO make sure these have no Read/Write terms *)
    List.combine ids ts
    |> List.fold_left (fun (eqs, state) (id, t) ->
        printf "\nExecuting assignment: %s := %s;\n" (string_of_ident id) (string_of_term t);
        let sm = IdMap.singleton id (mk_var_like id) in
        let t' = subst_term sm t in
        let (pure, spatial) = subst_state sm state in
        let eqs = add_eq id t' (subst_eqs sm eqs) in
        eqs, (pure, spatial)
      ) (eqs, state)
  | Basic (Call {call_lhs=lhs; call_name=foo; call_args=args}, _) ->
    Debug.info (fun () ->
      sprintf "\nExecuting function call: %s%s(%s);\n"
        (match (lhs |> List.map string_of_ident |> String.concat ", ") with
        | "" -> ""
        | str -> str ^ " := ")
        (string_of_ident foo) (args |> List.map string_of_term |> String.concat ", ")
    );
    (* Look up pre/post of foo *)
    let foo_pre, foo_post =
      (* TODO optimize by precomputing this. *)
      let c = (find_proc prog foo).proc_contract in
      (* Substitute formal params -> actual params in foo_pre/post *)
      let sm = mk_eqs c.contr_formals args in
      let pre = c.contr_precond |> state_of_spec_list |> subst_state sm in
      (* TODO: unsound if ints passed by value? *)
      (* Also substitute return vars -> lhs vars in post *)
      let sm =
        List.fold_left2 (fun sm r l -> IdMap.add r (mk_const_term l) sm)
          sm c.contr_returns lhs
      in
      let post = c.contr_postcond |> state_of_spec_list |> subst_state sm in
      remove_useless_existentials pre, remove_useless_existentials post
    in
    Debug.info (fun () ->
      sprintf "  Found contract:\n    precondition: %s\n    postcondition: %s\n"
        (string_of_state foo_pre) (string_of_state foo_post)
    );
    let foo_pre = apply_equalities eqs foo_pre in
    let frame, inst = find_frame eqs state foo_pre in
    Debug.info (fun () -> sprintf "\n  Found frame: %s\n"
        (frame |> List.map string_of_spatial_pred |> String.concat " &*& ")
    );
    (* Then, create vars for old vals of all x in lhs, and substitute in eqs & frame *)
    let sm =
      lhs |> List.fold_left (fun sm id ->
          IdMap.add id (mk_var_like id) sm)
        IdMap.empty
    in
    let eqs = subst_eqs sm eqs in
    let frame = List.map (subst_spatial_pred sm) frame in
    if IdMap.is_empty inst |> not then
      printf "WARNING: Ignoring inst from find_frame: %s" (string_of_equalities inst);
    let (pure, spatial) = state in
    let (post_pure, post_spatial) = foo_post in
    let state = (smk_and [pure; post_pure], post_spatial @ frame) in
    Debug.info (fun () -> sprintf "\n  New state: %s : %s\n"
      (string_of_equalities eqs) (string_of_state state)
    );
    eqs, state
  | Seq (comms, _) ->
    List.fold_left (symb_exec prog proc) (eqs, state) comms
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
    let eqs, state = symb_exec prog proc (eqs, precond) comm in
    check_entailment eqs state postcond
  | None ->
    []

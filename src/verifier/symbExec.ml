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
  | PointsTo of term * sort * (ident * term) list  (** x |-> [f1: E1, ..] *)
  | Pred of ident * term list
  | Dirty of spatial_pred list * term list  (** Dirty region: [f1 * ..]_(e1, ..) *)

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


(* TODO use Format formatters for these *)
let rec string_of_spatial_pred = function
  | PointsTo (x, _, fs) ->
    sprintf "%s |-> (%s)" (string_of_term x)
      (fs |> List.map (fun (id, t) -> (string_of_ident id) ^ ": " ^ (string_of_term t))
        |> String.concat ", ")
  | Pred (id, ts) ->
    sprintf "%s(%s)" (string_of_ident id)
      (ts |> List.map string_of_term |> String.concat ", ")
  | Dirty (fs, ts) ->
    sprintf "[%s]_(%s)" (string_of_spatial_pred_list fs) (ts |> List.map string_of_term |> String.concat ", ")

and string_of_spatial_pred_list sps =
  sps |> List.map string_of_spatial_pred |> String.concat " * "

let string_of_state ((pure, spatial): state) =
  let spatial =
    match spatial with
    | [] -> "emp"
    | spatial -> string_of_spatial_pred_list spatial
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
  Assumes [fields] is a set of field identifiers, all other maps are treated as
  functions.
*)
let state_of_spec_list fields specs : state =
  (** [reads] is a map: location -> field -> new var, for every field read
    Sorry for using refs, but didn't know how to map and fold terms simultaneously
  *)
  let reads = ref TermMap.empty in
  let rec convert_term = function
    | Var _ as t -> t
    | App (Read, [App (FreeSym fld, [], _); loc], srt) 
        when IdSet.mem fld fields -> (* loc.fld *)
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
    | App (Read, [f; arg], srt) -> (* function application: f(arg) *)
      (* Assuming f itself does not contain field reads terms
        - i.e. can't store functions in heap *)
      App (Read, [f; convert_term arg], srt)
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
    | Sl.Atom (Sl.Region, [(App (SetEnum, [x], Set Loc srt))], _) -> (* acc(x) *)
      let x = convert_term x in
      (pure, PointsTo (x, srt, []) :: spatial)
    | Sl.Atom (Sl.Region, ts, _) -> fail ()
    | Sl.Atom (Sl.Pred p, ts, _) ->
      (pure, Pred (p, ts) :: spatial)
    | Sl.SepOp (Sl.SepStar, f1, f2, _) ->
      let (pure, spatial) = convert_sl_form (pure, spatial) f2 in
      convert_sl_form (pure, spatial) f1
    | Sl.SepOp (Sl.SepIncl, _, _, _) -> fail ()
    | Sl.SepOp (Sl.SepPlus, _, _, _) -> fail ()
    | Sl.BoolOp _ -> fail ()
    | Sl.Binder (b, vs, f, _) ->
      print_endline "\n\nWARNING: TODO: make substitutions capture avoiding!\n";
      let pure1, spatial1 = convert_sl_form empty_state f in
      (match spatial1 with
      | [] -> (smk_and [smk_binder b vs pure1; pure], spatial)
      | _ ->
        failwith @@ "Confused by spatial under binder: " ^ (Sl.string_of_form f))
    | Sl.Dirty (f, ts, _) ->
      let pure1, spatial1 = convert_sl_form empty_state f in
      smk_and [pure1; pure], Dirty (spatial1, ts) :: spatial
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
    let rec put_reads = function
      | PointsTo (x, s, fs) ->
        let fs' =
          try TermMap.find x reads |> IdMap.bindings with Not_found -> []
        in
        PointsTo (x, s, fs @ fs')
      | Pred _ as p -> p
      | Dirty (sps, ts) -> Dirty (List.map put_reads sps, ts)
    in
    List.map put_reads spatial
  in
  (* TODO check the following in presence of x.next.next etc *)
  (* If we have a points-to atom without a corresponding acc() in reads, fail *)
  let alloc_terms =
    let rec collect_allocs allocs = function
    | PointsTo (x, _, _) -> TermSet.add x allocs
    | Pred _ -> allocs
    | Dirty (sps, ts) -> List.fold_left collect_allocs allocs sps
    in
    List.fold_left collect_allocs TermSet.empty spatial
  in
  if TermMap.exists (fun t _ -> TermSet.mem t alloc_terms |> not) reads then
    failwith "state_of_spec_list: couldn't find corresponding acc"
  else
    (pure, spatial)


(** Substitute both vars and constants in a term according to [sm]. *)
let subst_term sm = subst_consts_term sm >> subst_term sm

(** Substitute both vars and constants in a form according to [sm]. *)
let subst_form sm = subst_consts sm >> subst sm

let rec subst_spatial_pred sm = function
  | PointsTo (id, s, fs) ->
    PointsTo (subst_term sm id, s, List.map (fun (id, t) -> id, subst_term sm t) fs)
  | Pred (id, ts) ->
    Pred (id, List.map (subst_term sm) ts)
  | Dirty (sps, ts) ->
    Dirty (List.map (subst_spatial_pred sm) sps, List.map (subst_term sm) ts)

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

(** Add implicit disequalities from spatial to pure. Assumes normalized by eq. *)
let add_neq_constraints (pure, spatial) =
  let allocated =
    let rec find_alloc = function
    | PointsTo (x, s, _) -> [(x, s)]
    | Dirty (sp', _) -> List.map find_alloc sp' |> rev_concat
    | Pred _ -> []
    in
    List.map find_alloc spatial |> rev_concat
  in
  let not_nil = List.map (fun (x, s) -> mk_neq x (mk_null s)) allocated in
  let star_neq =
    let rec f acc = function
      | [] -> []
      | (x, _) :: l ->
        let acc = List.fold_left (fun neqs (y, _) -> mk_neq x y :: neqs) acc l in
        f acc l
    in
    f [] allocated
  in
  (smk_and (pure :: not_nil @ star_neq), spatial)


(** ----------- Symbolic Execution ---------- *)


(** Returns [(fs, spatial')] s.t. [spatial] = [loc] |-> [fs] :: [spatial'] *)
let find_ptsto loc spatial =
  let sp1, sp2 =
    List.partition (function | PointsTo (x, _, _) -> x = loc | Pred _ | Dirty _-> false)
      spatial
  in
  match sp1 with
  | [PointsTo (_, s, fs)] -> Some (fs, sp2)
  | [] -> None
  | _ ->
    failwith @@ "find_ptsto was confused by " ^
      (sp1 |> List.map string_of_spatial_pred |> String.concat " &*& ")

(** Finds a points-to predicate at location [loc] in [spatial], including in dirty regions.
  If found, returns [(Some fs, repl_fn)] such that
  [loc] |-> [fs] appears in [spatial]
  and [repl_fn fs'] returns [spatial] with [fs] replaced by [fs'] *)
let rec find_ptsto_dirty loc spatial =
  match spatial with
  | [] -> None, (fun fs' -> spatial)
  | PointsTo (x, s, fs) :: spatial' when x = loc ->
    Some fs, (fun fs' -> PointsTo (x, s, fs') :: spatial')
  | Dirty (f, ts) as sp :: spatial' ->
    let res, repl_fn = find_ptsto_dirty loc f in
    (match res with
    | Some fs -> Some fs, (fun fs' -> Dirty (repl_fn fs', ts) :: spatial')
    | None -> 
      let res, repl_fn = find_ptsto_dirty loc spatial' in
      res, (fun fs' -> sp :: repl_fn fs')
    )
  | sp :: spatial' ->
    let res, repl_fn = find_ptsto_dirty loc spatial' in
    res, (fun fs' -> sp :: repl_fn fs')

let check_pure_entail eqs p1 p2 =
  let (p2, _) = apply_equalities eqs (p2, []) |> remove_useless_existentials in
  if p1 = p2 || p2 = mk_true then true
  else (* Dump it to an SMT solver *)
    (* Close the formulas: Assuming all free variables are existential *)
    (* TODO nnf? *)
    let close f = smk_exists (IdSrtSet.elements (sorted_free_vars f)) f in
    let f = smk_and [close p1; mk_not (close p2)] in
    match Prover.get_model f with
    | None -> true
    | Some model ->
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
    if check_pure_entail (IdMap.union (fun _ -> failwith "") eqs inst) p1 p2 then
      sp1, inst
    else fail ()
  | PointsTo (x, _, fs2) :: sp2' ->
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
  | Dirty (sp2a, ts) :: sp2b ->
    (* Find a Dirty region in sp1 with same interface ts *)
    let sp1a, sp1b =
      List.partition (function | Dirty (_, ts') when ts = ts' -> true | _ -> false) sp1
    in
    (match sp1a with
    | [Dirty (sp1a, _)] ->
      let res, inst = check_entailment ~inst:inst eqs (mk_true, sp1a) (mk_true, sp2a) in
      if res = [] then
        find_frame ~inst:inst eqs (p1, sp1b) (p2, sp2b)
      else failwith @@ sprintf "find_frame: couldn't match up the inside of the dirty region"
    | _ -> todo ()
    )
  | _ ->
    todo ()


and check_entailment ?(inst=empty_eqs) eqs (p1, sp1) (p2, sp2) =
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
  | [] -> [], inst
  | _ -> failwith @@ sprintf "Frame was not empty: %s" (string_of_state (mk_true, fr))


(** Evaluate term at [state] by looking up all field reads.
  Assumes term has already been normalized w.r.t eqs *)
let rec eval_term fields state = function
  | Var _ as t -> (t, state)
  | App (Read, [App (FreeSym fld, [], _); App (FreeSym _, [], _) as loc], srt)
      as t when IdSet.mem fld fields ->
    Debug.info (fun () -> sprintf "\nExecuting lookup: %s\n" (string_of_term t));
    let loc, state = eval_term fields state loc in
    (match find_ptsto_dirty loc (snd state) with
    | Some fs, mk_spatial' ->
      (* lookup fld in fs, so that loc |-> fs' and (fld, e) is in fs' *)
      let e, fs' =
        try List.assoc fld fs, fs
        with Not_found -> let e = mk_fresh_var srt "v" in e, (fld, e) :: fs
      in
      let spatial' = mk_spatial' fs' in
      e, (fst state, spatial')
    | None, _ -> failwith "Invalid lookup"
    )
  | App (Write, _, _) as t ->
    failwith @@ "eval_term called on write " ^ (string_of_term t)
  | App (s, ts, srt) ->
    let ts, state = fold_left_map (eval_term fields) state ts in
    App (s, ts, srt), state


(** Symbolically execute command [comm] on state [state] and return final state. *)
let rec symb_exec prog flds proc (eqs, state) comm =
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
  | Basic (Assign {assign_lhs=[fld];
      assign_rhs=[App (Write, [App (FreeSym fld', [], _); 
        App (FreeSym _, [], _) as loc; rhs], srt)]}, _) when fld = fld' ->
    Debug.info (fun () ->
      sprintf "\nExecuting mutate: %s.%s := %s;\n" (string_of_term loc)
        (string_of_ident fld) (string_of_term rhs)
    );
    (* First, substitute eqs on loc and rhs *)
    let loc = subst_term eqs loc and rhs = subst_term eqs rhs in
    (* Then, evaluate rhs in case it contains lookups *)
    let rhs, (pure, spatial) = eval_term flds state rhs in
    (* Find the node to mutate *)
    (match find_ptsto_dirty loc spatial with
    | Some fs, mk_spatial' ->
      (* mutate fs to fs' so that it contains (fld, rhs) *)
      let fs' =
        if List.exists (fst >> (=) fld) fs
        then List.map (fun (f, e) -> (f, if f = fld then rhs else e)) fs
        else (fld, rhs) :: fs
      in
      eqs, (pure, mk_spatial' fs')
    | None, _ -> failwith @@ "Invalid write: " ^ (comm |> source_pos |> string_of_src_pos)
    )
  | Basic (Assign {assign_lhs=ids; assign_rhs=ts}, _) ->
    (* TODO simultaneous assignments can't touch heap, so do all at once *)
    List.combine ids ts
    |> List.fold_left (fun (eqs, state) (id, t) ->
        printf "\nExecuting assignment: %s := %s;\n" (string_of_ident id) (string_of_term t);
        (* Eval t in case it has field lookups *)
        let t, state = eval_term flds state t in
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
      let pre = c.contr_precond |> state_of_spec_list flds |> subst_state sm in
      (* TODO: unsound if ints passed by value? *)
      (* Also substitute return vars -> lhs vars in post *)
      let sm =
        List.fold_left2 (fun sm r l -> IdMap.add r (mk_const_term l) sm)
          sm c.contr_returns lhs
      in
      let post = c.contr_postcond |> state_of_spec_list flds |> subst_state sm in
      remove_useless_existentials pre, remove_useless_existentials post
    in
    Debug.info (fun () ->
      sprintf "  Found contract:\n    precondition: %s\n    postcondition: %s\n"
        (string_of_state foo_pre) (string_of_state foo_post)
    );
    (* Add derived equalities before checking for frame & entailment *)
    (* TODO do this by keeping disequalities in state? *)
    let state = add_neq_constraints state in
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
    let (pure, spatial) = state in
    let (post_pure, post_spatial) = foo_post in
    let state = (smk_and [pure; post_pure], post_spatial @ frame) in
    Debug.info (fun () -> sprintf "\n  New state: %s : %s\n"
      (string_of_equalities eqs) (string_of_state state)
    );
    eqs, state
  | Seq (comms, _) ->
    List.fold_left (symb_exec prog flds proc) (eqs, state) comms
  | Basic (Havoc {havoc_args=vars}, _) ->
    (* Just substitute all occurrances of v for new var v' in symbolic state *)
    Debug.info (fun () ->
      sprintf "\nExecuting havoc: havoc(%s);\n"
        (vars |> List.map string_of_ident |> String.concat ", ")
    );
    let sm =
      List.fold_left (fun sm v -> IdMap.add v (mk_var_like v) sm) 
        IdMap.empty vars
    in
    (subst_eqs sm eqs, subst_state sm state)
  | Basic (Assume {spec_form=FOL spec}, _) ->
    (* Pure assume statements are just added to pure part of state *)
    let spec = spec |> filter_annotations (fun _ -> false) |> subst_form eqs in
    Debug.info (fun () ->
      sprintf "\nExecuting assume: assume(%s);\n" (string_of_form spec)
    );
    let (pure, spatial) = state in
    let spec, state = fold_map_terms (eval_term flds) state spec in
    (eqs, (smk_and [pure; spec], spatial))
  | Basic (Assume _, _) -> failwith "TODO Assume SL command"
  | Basic (New _, _) -> failwith "TODO New command"
  | Basic (Dispose _, _) -> failwith "TODO Dispose command"
  | Basic (Assert _, _) -> failwith "TODO Assert command"
  | Basic (Return _, _) -> failwith "TODO Return command"
  | Loop _ -> failwith "TODO Loop command"
  | Choice _ -> failwith "TODO Choice command"


(** Check procedure [proc] in program [prog] using symbolic execution. *)
let check spl_prog prog proc =
  Debug.info (fun () ->
      "Checking procedure " ^ string_of_ident (name_of_proc proc) ^ "...\n");

  (* Extract the list of field names from the spl_prog. *)
  let flds =
    IdMap.fold (fun _ tdecl flds ->
      match tdecl.SplSyntax.t_def with
      | SplSyntax.StructTypeDef vs ->
        IdMap.fold (fun id _ flds -> IdSet.add id flds) vs flds
      | _ -> flds
    ) spl_prog.SplSyntax.type_decls IdSet.empty
  in
  match proc.proc_body with
  | Some comm ->
    let precond = state_of_spec_list flds proc.proc_contract.contr_precond in
    let postcond = state_of_spec_list flds proc.proc_contract.contr_postcond in
    Debug.info (fun () ->
      sprintf "  Precondition: %s\n  Postcondition: %s\n"
        (string_of_state precond) (string_of_state postcond)
    );

    let eqs = empty_eqs in
    let eqs, state = symb_exec prog flds proc (eqs, precond) comm in
    Debug.info (fun () -> "\nChecking postcondition...\n");
    (* TODO do this better *)
    let state = add_neq_constraints state in
    check_entailment eqs state postcond |> fst
  | None ->
    []

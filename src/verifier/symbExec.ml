(** {5 Symbolic execution based verifier} *)

open Util
open Grass
open GrassUtil
open Prog
open Printf

let simplify proc prog =
  prog |>
  dump_if 0 |>
  Analyzer.infer_accesses true |>
  Simplifier.elim_loops |>
  Simplifier.elim_global_deps |>
  dump_if 1 
  
exception NotYetImplemented
let todo () = raise NotYetImplemented

exception SymbExecFail of string
let raise_err str = raise (SymbExecFail str)

let lineSep = "\n--------------------\n"

let fresh_array_length () = mk_free_const Int (fresh_ident "array_length")

let fresh_array_map srt = mk_free_const (Map ([Int], srt)) (fresh_ident "array_map")

(* TODO use consts instead? And use idents instead of terms in spatial_pred *)
let fresh_const srt = mk_var srt (fresh_ident "v")

(** ----------- Symbolic state and manipulators ---------- *)

type spatial_pred =
  | PointsTo of term * (ident * term) list  (** x |-> [f1: E1, ..] *)
  | Pred of ident * term list
  | Arr of term * term * term  (** Array(address, length, map) *)
  | Conj of spatial_pred list list  (** Conjunction of spatial states *)

(** A symbolic state is a (pure formula, a list of spatial predicates).
  Note: program vars are represented as FreeSymb constants,
  existential vars are represented as Var variables.
 *)
type state = {
    pure: form;
    spatial: spatial_pred list
  }

let mk_pure_state p = { pure = p; spatial = [] }
let mk_spatial_state sp = { pure = mk_true; spatial = sp }
    
let empty_state = { pure = mk_true; spatial = [] }

let map_state_pure fn state =
  { state with pure = fn state.pure }
let map_state_spatial fn state =
  { state with spatial = fn state.spatial }
let map_state pfn sfn state =
  { pure = pfn state.pure; spatial = sfn state.spatial }

let strengthen_pure_state fs state =
  map_state_pure (fun pure -> smk_and (pure :: fs)) state
    
(** Conjoin two states *)
let add_state s1 s2 =
  { pure = smk_and [s1.pure; s2.pure];
    spatial = s1.spatial @ s2.spatial
  }

    
(** Equalities derived so far in the symbolic execution, as a map: ident -> term,
  kept so that they can be substituted into the command and the post.
  Invariant: if map is {x1: E1, ...} then xi are distinct and xi is not in Ej for i != j.
  ASSUMES: vars and constants do not share names!
  TODO: can we make it ident IdMap.t now?
  *)
type equalities = term IdMap.t

(** The state of the symbolic execution engine *)
type symb_exec_state = {
  se_state: state;
  se_prog: program;
  se_proc: proc_decl;
  se_fields: IdSet.t;
  se_eqs: equalities;
}

let empty_eqs = IdMap.empty

let update_se_state st state = { st with se_state = state }

(* TODO use Format formatters for these *)
let rec string_of_spatial_pred = function
  | PointsTo (x, fs) ->
    sprintf "%s |-> (%s)" (string_of_term x)
      (fs |> List.map (fun (id, t) -> (string_of_ident id) ^ ": " ^ (string_of_term t))
        |> String.concat ", ")
  | Pred (id, ts) ->
    sprintf "%s(%s)" (string_of_ident id)
      (ts |> List.map string_of_term |> String.concat ", ")
  | Arr (x, l, m) ->
    sprintf "arr(%s, %s, %s)" (string_of_term x) (string_of_term l) (string_of_term m)
  | Conj fss ->
    List.map (function
        | [p] -> string_of_spatial_pred p
        | ps -> "(" ^ string_of_spatial_pred_list ps ^ ")"
      ) fss
    |> String.concat " && "

and string_of_spatial_pred_list sps =
  sps |> List.map string_of_spatial_pred |> String.concat " * "

let string_of_state (s: state) =
  let spatial =
    match s.spatial with
    | [] -> "emp"
    | spatial -> string_of_spatial_pred_list spatial
  in
  let pure = s.pure
    |> filter_annotations (fun _ -> false)
    |> string_of_form
    (* |> String.map (function | '\n' -> ' ' | c -> c) *)
  in
  sprintf "Pure: %s\nSpatial: %s" pure spatial

let string_of_equalities eqs =
  IdMap.bindings eqs
  |> List.map (fun (x, t) -> (string_of_ident x) ^ " = " ^ (string_of_term t))
  |> String.concat ", "
  |> sprintf "{%s}"

let string_of_se_state st =
  sprintf "Eqs: %s\n%s" (string_of_equalities st.se_eqs) (string_of_state st.se_state)


(** Finds a points-to predicate at location [loc] in [spatial], including in dirty regions.
  If found, returns [(Some fs, repl_fn_rd, repl_fn_wr)] such that
  [loc] |-> [fs] appears in [spatial]
  [repl_fn_rd fs'] returns [spatial] with [fs] replaced by [fs']
  and [repl_fn_wr fs'] returns [spatial] with [fs] replaced by [fs'],
    but if [fs] appears in a Conj, then it drops all other conjuncts *)
let rec find_ptsto loc spatial =
  match spatial with
  | [] ->
    let repl_fn = (fun fs' -> spatial) in
    None, repl_fn, repl_fn
  | PointsTo (x, fs) :: spatial' when x = loc ->
    let repl_fn = (fun fs' -> PointsTo (x, fs') :: spatial') in
    Some fs, repl_fn, repl_fn
  | Conj spss as sp :: spatial' ->
    let rec find_conj spss1 = function
      | sps :: spss2 ->
        (match find_ptsto loc sps with
        | Some fs, repl_fn_rd, repl_fn_wr ->
          let repl_fn_rd = (fun fs' -> Conj (repl_fn_rd fs' :: spss1 @ spss2) :: spatial') in
          let repl_fn_wr = (fun fs' -> repl_fn_wr fs' @ spatial') in
          Some fs, repl_fn_rd, repl_fn_wr
        | None, _, _ ->
          find_conj (sps :: spss1) spss2)
      | [] -> todo ()
    in
    (match find_conj [] spss with
    | Some _, _, _ as res -> res
    | None, _, _ ->
      let res, repl_fn_rd, repl_fn_wr = find_ptsto loc spatial' in
      res, (fun fs' -> sp :: repl_fn_rd fs'), (fun fs' -> sp :: repl_fn_wr fs')
    )
  | sp :: spatial' ->
    let res, repl_fn_rd, repl_fn_wr = find_ptsto loc spatial' in
    res, (fun fs' -> sp :: repl_fn_rd fs'), (fun fs' -> sp :: repl_fn_wr fs')


(** Finds an array predicate at location [loc] in [spatial], including in dirty regions.
  If found, returns [(Some m, repl_fn_wr)] such that
  [arr(loc, _, m)] appears in [spatial]
  and [repl_fn_wr m'] returns [spatial] with [m] replaced by [m'],
    but if [loc] appears in a Conj, then it drops all other conjuncts *)
let rec find_array loc spatial =
  match spatial with
  | [] ->
    let repl_fn = (fun fs' -> spatial) in
    None, repl_fn
  | Arr (x, l, m) :: spatial' when x = loc ->
    let repl_fn = (fun m' -> Arr(x, l, m') :: spatial') in
    Some (l, m), repl_fn
  | Conj spss as sp :: spatial' ->
    let rec find_conj spss1 = function
      | sps :: spss2 ->
        (match find_array loc sps with
        | Some lm, repl_fn_wr ->
          let repl_fn_wr = (fun fs' -> repl_fn_wr fs' @ spatial') in
          Some lm, repl_fn_wr
        | None, _ ->
          find_conj (sps :: spss1) spss2)
      | [] -> todo ()
    in
    (match find_conj [] spss with
    | Some _, _ as res -> res
    | None, _ ->
      let res, repl_fn_wr = find_array loc spatial' in
      res, (fun fs' -> sp :: repl_fn_wr fs')
    )
  | sp :: spatial' ->
    let res, repl_fn_wr = find_array loc spatial' in
    res, (fun fs' -> sp :: repl_fn_wr fs')


(* Special find_ptsto for extracting and removing a PointsTo from spatial' *)
let find_ptsto_spatial' x =
  find_map_res (function PointsTo(x', fs') when x = x' -> Some fs' | _ -> None)

(* Special find_ptsto for extracting and removing an Arr from spatial' *)
let find_arr_spatial' x =
  find_map_res (function Arr(x', l, m) when x = x' -> Some (l, m) | _ -> None)

(** Evaluate term at [state] by looking up all field reads.
  [old_state] is the state with which to evaluate old(x) terms.
  [spatial'] is the list of spatial preds needed to evaluate everything in [t]. *)
let rec eval_term fields (old_state, (state: state), spatial') = function
  | Var _ as t -> t, (old_state, state, spatial')
  | App (Read, [App (FreeSym fld, [], _); loc], srt)
    when IdSet.mem fld fields -> (* Field reads *)
    let loc, (old_state, state, spatial') = eval_term fields (old_state, state, spatial') loc in
    (match find_ptsto loc state.spatial with
    | Some fs, mk_spatial, _ ->
      (* lookup fld in fs, so that loc |-> fs' and (fld, e) is in fs' *)
      let e, fs' =
        try List.assoc fld fs, fs
        with Not_found ->
          let e = fresh_const srt in e, (fld, e) :: fs
      in
      let state' = map_state_spatial (fun _ -> mk_spatial fs') state in
      e, (old_state, state', spatial')
    | None, _, _ ->
      (match find_ptsto_spatial' loc spatial' with
      | Some (fs, spatial') -> 
        (* lookup fld in fs, so that loc |-> fs' and (fld, e) is in fs' *)
        let e, fs' =
          try List.assoc fld fs, fs
          with Not_found ->
            let e = fresh_const srt in e, (fld, e) :: fs
        in
        e, (old_state, state, PointsTo (loc, fs') :: spatial')
      | None -> (* Add loc to spatial' to indicate we need an acc(loc) in the future *)
        let e = fresh_const srt in
        e, (old_state, state, PointsTo (loc, [fld, e]) :: spatial')))
  | App (Read, [a; idx], srt)
      when sort_of a = Loc (Array srt) ->
        (* Array reads *)
    let a, (old_state, state, spatial') = eval_term fields (old_state, state, spatial') a in
    let idx, (old_state, state, spatial') = eval_term fields (old_state, state, spatial') idx in
    let m, spatial' =
    (match find_array a state.spatial with
    | Some (_, m), _ -> m, spatial'
    | None, _ -> (* If you can't find a in spatial, look in/add it to spatial' *)
      (match find_arr_spatial' a spatial' with
      | Some ((l, m), spatial') ->
        m, Arr (a, l, m) :: spatial'
      | None ->
        let l = fresh_array_length () in
        let m = fresh_array_map srt in
        m, Arr (a, l, m) :: spatial'))
    in
    mk_read m [idx], (old_state, state, spatial')
  | App (Length, [a], _) ->
    let a, (old_state, state, spatial') = eval_term fields (old_state, state, spatial') a in
    let l, spatial' =
    (match find_array a state.spatial with
    | Some (l, _), _ -> l, spatial'
    | None, _ -> (* If you can't find a in spatial, look in/add it to spatial' *)
      (match find_arr_spatial' a spatial' with
      | Some ((l, m), spatial') ->
        l, Arr (a, l, m) :: spatial'
      | None ->
        let l = fresh_array_length () in
        let srt = match (sort_of a) with | Loc Array s -> s | _ -> assert false in
        let m = fresh_array_map srt in
        l, Arr (a, l, m) :: spatial'))
    in
    l, (old_state, state, spatial')
  | App (ArrayMap, [a], _) ->
    let a, (old_state, state, spatial') = eval_term fields (old_state, state, spatial') a in
    let m, spatial' =
    (match find_array a state.spatial with
    | Some (_, m), _ -> m, spatial'
    | None, _ -> (* If you can't find a in spatial, look in/add it to spatial' *)
      (match find_arr_spatial' a spatial' with
      | Some ((l, m), spatial') ->
        m, Arr (a, l, m) :: spatial'
      | None ->
        let l = fresh_array_length () in
        let srt = match (sort_of a) with | Loc Array s -> s | _ -> assert false in
        let m = fresh_array_map srt in
        m, Arr (a, l, m) :: spatial'))
    in
    m, (old_state, state, spatial')
  | App (Old, [t], srt) as t' ->
    (* Eval t using old_state as state *)
    (match old_state with
    | Some old_state -> 
      let t, (_, old_state, spatial') = eval_term fields (None, old_state, spatial') t in
      t, (Some old_state, state, spatial')
    | None -> raise_err @@ "Unexpected old term: " ^ (string_of_term t'))
  | App (s, ts, srt) ->
    let ts, (old_state, state, spatial') = fold_left_map (eval_term fields) (old_state, state, spatial') ts in
    App (s, ts, srt), (old_state, state, spatial')

let eval_term_no_olds fields state term =
  match eval_term fields (None, state, []) term with
    | term, (_, state, []) -> term, state
    | _, (_, _, x :: _) ->
      raise_err @@ "Possible invalid heap lookup. Couldn't find: " ^ (string_of_spatial_pred x)


(** Convert a specification into a symbolic state.
  This also moves field read terms from pure formula to points-to predicates.
  Assumes [fields] is a set of field identifiers, all other maps are treated as
  functions.
*)
let state_of_spec_list fields old_state specs : state * state =
  let eval_term = eval_term fields in
  let add (pure, spatial) = add_state { pure = pure; spatial = spatial } in
  (* [spatial'] is a list of outstanding spatial_preds needed to eval [state] *)
  let convert_form (old_state, state, spatial') f =
    let f, (old_state, (state: state), spatial') =
      fold_map_terms eval_term (old_state, state, spatial') f
    in
    (old_state, add (f, []) state, spatial')
  in
  let rec convert_sl_form (old_state, (state: state), spatial') f =
    let fail () = failwith @@ "Unsupported formula " ^ (Sl.string_of_form f) in
    match f with
    | Sl.Pure (f, _) -> convert_form (old_state, state, spatial') f
    | Sl.Atom (Sl.Emp, ts, _) -> old_state, state, spatial'
    | Sl.Atom (Sl.Region, [(App (SetEnum, [x], Set Loc Array srt))], _) -> (* arr(x) *)
      let x, (old_state, state, spatial') = eval_term (old_state, state, spatial') x in
      (* First check if we've already created it in spatial' *)
      let l, m, spatial' =
        (match find_arr_spatial' x spatial' with
        | Some ((l, m), spatial') ->
          l, m, spatial'
        | None ->
          let l = fresh_array_length () in
          let m = fresh_array_map srt in
          l, m, spatial')
      in
      let len_axiom = mk_leq (mk_int 0) l in
      old_state, add (len_axiom, [Arr (x, l, m)]) state, spatial'
    | Sl.Atom (Sl.Region, [(App (SetEnum, [x], Set Loc _))], _) -> (* acc(x) *)
      let x, (old_state, state, spatial') = eval_term (old_state, state, spatial') x in
      (* First check if we've already created it in spatial' *)
      let sp, spatial' =
        (match find_ptsto_spatial' x spatial' with
        | Some (fs, spatial') -> PointsTo (x, fs), spatial'
        | None -> PointsTo (x, []), spatial')
      in
      old_state, add (mk_true, [sp]) state, spatial'
    | Sl.Atom (Sl.Region, ts, _) -> fail ()
    | Sl.Atom (Sl.Pred p, ts, _) ->
      old_state, add (mk_true, [Pred (p, ts)]) state, spatial'
    | Sl.SepOp (Sl.SepStar, f1, f2, _) ->
      List.fold_left convert_sl_form (old_state, state, spatial') [f1; f2]
    | Sl.SepOp (Sl.SepIncl, _, _, _) -> fail ()
    | Sl.SepOp (Sl.SepPlus, _, _, _) -> fail ()
    | Sl.BoolOp (And, fs, _) ->
      let old_state, conj_states, spatial' =
        List.fold_left (fun (old_state, conj_states, spatial') f ->
            let old_state, state', spatial' =
              convert_sl_form (old_state, empty_state, spatial') f
            in
            old_state, state' :: conj_states, spatial')
          (old_state, [], spatial') fs
      in
      let pures, spatials =
        conj_states |>
        List.map (function {pure = p; spatial = s; _ } -> (p, s)) |>
        List.split
      in
      let spatials = List.filter (function [] -> false | _ -> true) spatials in
      (match spatials with
      | [] -> old_state, add (smk_and pures, []) state, spatial'
      | [sp] -> old_state, add (smk_and pures, sp) state, spatial'
      | _ -> old_state, add (smk_and pures, [Conj spatials]) state, spatial')
    | Sl.BoolOp _ -> fail ()
    | Sl.Binder (b, vs, f, _) ->
      let old_state, state1, spatial' =
        convert_sl_form (old_state, mk_spatial_state state.spatial, spatial') f
      in
      if state1.spatial = state.spatial then
        old_state, add (smk_binder b vs state1.pure, []) state, spatial'
      else
        failwith @@ "Confused by spatial under binder: " ^ (Sl.string_of_form f)
  in
  (* Convert all the specs into a state *)
  let (old_state, state, spatial') =
    List.fold_left (fun (old_state, state, spatial') spec ->
        let f =
          match spec.spec_form with
          | SL f -> f
          | FOL f -> Sl.Pure (f, None)
        in
        convert_sl_form (old_state, state, spatial') f
      ) (old_state, empty_state, []) specs
  in
  (* Make sure there's nothing left in spatial' *)
  (match spatial' with
  | [] -> ()
  | (PointsTo(x, _) | Arr (x, _, _)) :: _ ->
    raise_err @@ "Possible invalid heap lookup to address: " ^ (string_of_term x)
  | _ -> todo ());
  Opt.get_or_else empty_state old_state, state


(** Substitute both vars and constants in a term according to [sm]. *)
let subst_term sm = subst_consts_term sm >> subst_term sm

(** Substitute both vars and constants in a form according to [sm]. *)
let subst_form sm = subst_consts sm >> subst sm

let rec subst_spatial_pred sm = function
  | PointsTo (id, fs) ->
    PointsTo (subst_term sm id, List.map (fun (id, t) -> id, subst_term sm t) fs)
  | Pred (id, ts) ->
    Pred (id, List.map (subst_term sm) ts)
  | Arr (x, l, m) ->
    Arr (subst_term sm x, subst_term sm l, subst_term sm m)
  | Conj spss ->
    Conj (List.map (List.map (subst_spatial_pred sm)) spss)

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
  according to substitution map [sm]. *)
let subst_state sm {pure = pure; spatial = spatial; _} : state =
  { pure = subst_form sm pure;
    spatial = List.map (subst_spatial_pred sm) spatial }

(** Substitute all variables and constants in state [st] with terms
  according to substitution map [sm]. *)
let subst_se_state sm st =
  {st with se_eqs = subst_eqs sm st.se_eqs; se_state = subst_state sm st.se_state}


(** Given two lists of idents and terms, create an equalities/subst map out of them. *)
let mk_eqs ids terms =
  List.fold_left2 (fun eqs id t -> IdMap.add id t eqs) empty_eqs ids terms

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

(** Normalize a Conj by some kind of sorting *)
let sort_conj = function
  | Conj spss ->
    Conj (spss |> List.map (List.stable_sort compare) |> List.stable_sort compare)
  | sp -> sp

(** Find equalities of the form const == const in [state] and add to [eqs] *)
let find_equalities eqs state =
  let rec find_eq sm = function
    | Atom (App (Eq, [(App (FreeSym id, [],  _)); App (FreeSym _, [],  _) as t2], _), _) ->
      add_eq id t2 sm
    | BoolOp (And, fs) ->
      List.fold_left find_eq sm fs
    | Binder (_, [], f, _) -> find_eq sm f
    | _ -> sm
  in
  find_eq eqs state.pure

(** Find equalities of the form var == exp in [pure] and return id -> exp map. *)
let find_var_equalities (pure: form) =
  let rec find_eq sm = function
    | Atom (App (Eq, [Var (id, _); Var _ as t2], _), _)
    | Atom (App (Eq, [Var (id, _); App (FreeSym _, [], _) as t2], _), _)
    | Atom (App (Eq, [App (FreeSym _, [], _) as t2; Var (id, _)], _), _) ->
      if IdMap.mem id sm then sm (* TODO you really need to fix this.. *)
      else add_eq id t2 sm
    | BoolOp (And, fs) ->
      List.fold_left find_eq sm fs
    | Binder (_, [], f, _) -> find_eq sm f
    | _ -> sm
  in
  find_eq IdMap.empty pure

let rec remove_trivial_equalities = function
  | Atom (App (Eq, [t1; t2], _), _) as f -> if t1 = t2 then mk_true else f
  | BoolOp (op, fs) -> smk_op op (List.map remove_trivial_equalities fs)
  | Binder (b, vs, f, anns) -> Binder (b, vs, remove_trivial_equalities f, anns)
  | f -> f

let apply_equalities eqs state =
  state |>
  subst_state eqs |>
  map_state_pure remove_trivial_equalities

let remove_useless_existentials state : state =
  (* Note: can also use GrassUtil.foralls_to_exists for this *)
  apply_equalities (find_var_equalities state.pure) state

(** Kill useless existential vars in state [st], find equalities between constants,
  add to [st.se_eqs] and simplify. *)
let simplify_state st =
  let state =
    st.se_state |>
    map_state_pure nnf |>
    remove_useless_existentials
  in
  let eqs = find_equalities st.se_eqs state in
  {st with se_eqs = eqs; se_state = apply_equalities eqs state}

(** Add implicit disequalities from spatial to pure. Assumes normalized by eq. *)
let add_neq_constraints st =
  let rec f acc locs = function
    | PointsTo (x, _) :: sps | Arr (x, _, _) :: sps ->
      let acc1 = TermSet.fold (fun y acc ->
          if sort_of x = sort_of y then mk_neq x y :: acc else acc)
        locs acc 
      in
      f acc1 (TermSet.add x locs) sps
    | Pred _ :: sps ->
      f acc locs sps
    | Conj spss :: sps ->
      let acc, locs =
        List.fold_left (fun (acc, locs') sps ->
            let acc, locs1 = f acc locs sps in
            acc, TermSet.union locs' locs1)
          (acc, locs) spss
      in
      f acc locs sps
    | [] -> acc, locs
  in
  let { pure = pure; spatial = spatial; _ } = st.se_state in
  let neqs, locs = f [] TermSet.empty spatial in
  (* Also add x != nil for every location x *)
  let get_sort x = match sort_of x with
    | Loc s -> s
    | s ->
      failwith @@ sprintf "Spatial location %s has non Loc sort %s"
        (string_of_term x) (string_of_sort s)
  in
  let neqs =
    TermSet.fold (fun x acc -> mk_neq x (mk_null (get_sort x)) :: acc) locs neqs
  in
  let new_se_state = strengthen_pure_state neqs st.se_state in
  update_se_state st new_se_state



(** ----------- Symbolic Execution ---------- *)


(* Returns None if the entailment holds, otherwise Some (list of error messages, model) *)
let check_pure_entail st p1 p2 =
  let { pure = p2; _ } = apply_equalities st.se_eqs (mk_pure_state p2) in
  if p1 = p2 || p2 = mk_true then None
  else (* Dump it to an SMT solver *)
    let axioms =  (* Collect all program axioms *)
      Util.flat_map
        (fun sf ->
          let name =
            Printf.sprintf "%s_%d_%d"
              sf.spec_name sf.spec_pos.sp_start_line sf.spec_pos.sp_start_col
          in
          match sf.spec_form with FOL f -> [mk_name name f] | SL _ -> [])
        st.se_prog.prog_axioms
      |> List.map (subst_form st.se_eqs) (* Apply equalities in eqs *)
    in
    let p2 = Verifier.annotate_aux_msg "Related location" p2 in
    (* Close the formulas: assuming all free variables are existential *)
    let close f = smk_exists (IdSrtSet.elements (sorted_free_vars f)) f in
    let labels, f =
      smk_and [p1; mk_not p2] |> close |> nnf |> Verifier.finalize_form st.se_prog
      (* Add definitions of all referenced predicates and functions *)
      |> fun f -> f :: Verifier.pred_axioms st.se_prog
      (* Add axioms *)
      |> (fun fs -> smk_and (fs @ axioms))
      (* Add labels *)
      |> Verifier.add_labels
    in
    let name = fresh_ident "form" |> string_of_ident in
    Debug.debug (fun () ->
      sprintf "\n\nCalling prover with name %s\n" name);
    match Prover.get_model ~session_name:name f with
    | None -> None
    | Some model -> Some (Verifier.get_err_msg_from_labels model labels, model)


(** Returns (fr, inst) s.t. state1 |= state2 * fr, and
  inst accumulates an instantiation for existential variables in state2.
  Assumes that both states have been normalized w.r.t eqs and inst. *)
let rec find_frame st ?(inst=empty_eqs) state1 state2 =
  Debug.debugl 1 (fun () ->
    sprintf "\nFinding frame with %s for:\n%s\n|=\n%s &*& ??\n"
      (string_of_equalities inst)
      (string_of_spatial_pred_list state1.spatial) (string_of_spatial_pred_list state2.spatial)
  );
  let match_up_sp inst sp2 sp1 =
    match sp2, sp1 with
    | sp2, sp1 when (sort_conj sp2) = (sort_conj sp1) ->
      (* match equal elements (for Conj, do some normalization) *)
      Some inst
    | PointsTo (x, fs2), PointsTo (x', fs1) when x = x' ->
      let match_up_fields inst fs1 fs2 =
        let fs1, fs2 = List.sort compare fs1, List.sort compare fs2 in
        let rec match_up inst = function
          | (_, []) -> Some inst
          | (fe1 :: fs1', fe2 :: fs2') when fe1 = fe2 -> (* Remove equal stuff *)
            match_up inst (fs1', fs2')
          | ((f1, e1) :: fs1', (f2, e2) :: fs2') when f1 = f2 ->
            (* e1 != e2, so only okay if e2 is ex. var *)
            (* add e2 -> e1 to inst and sub in fs2' to make sure e2 has uniform value *)
            (match e2 with
            | Var (e2_id, _) ->
              let sm = IdMap.singleton e2_id e1 in
              let fs2' = List.map (fun (f, e) -> (f, subst_term sm e)) fs2' in
              assert (IdMap.mem e2_id inst |> not);
              match_up (IdMap.add e2_id e1 inst) (fs1', fs2')
            | App (FreeSym e2_id, [], _) ->
              print_endline @@ ":: " ^ (string_of_term e1) ^ " " ^ (string_of_term e2);
              failwith "TODO"
            | _ -> None)
          | ((f1, e1) :: fs1', (f2, e2) :: fs2')
              when compare (f1, e1) (f2, e2) < 0 ->
            (* RHS doesn't need to have all fields, so drop (f1, e1) *)
            match_up inst (fs1', (f2, e2) :: fs2')
          | (fs1, (f2, e2)::fs2') ->
            (* f2 not in LHS, so only okay if e2 is an ex. var *)
            (match e2 with
            | Var (e, s) ->
              (* So create new const c, add e -> c to inst, and sub fs2' with inst *)
              let c = fresh_const s in
              let fs2' = fs2' |>
                List.map (fun (f, t) -> (f, subst_term (IdMap.singleton e c) t)) 
              in
              match_up (IdMap.add e c inst) (fs1, fs2')
            | _ -> None)
        in
        match_up inst (fs1, fs2)
      in
      match_up_fields inst fs1 fs2
    | Arr (x2, l2, m2), Arr (x1, l1, m1) when x1 = x2 ->
      (match l2, m2 with
      | App (FreeSym l2_id, [], _), App (FreeSym m2_id, [], _)
      | Var (l2_id, _), Var (m2_id, _) ->
        let inst = inst |> IdMap.add l2_id l1 |> IdMap.add m2_id m1 in
        Some inst
      | _ -> None)
    | Conj spss2, Conj spss1 ->
      let match_up_conjunct inst sps2 sps1 =
        (match check_entailment st ~inst:inst (mk_spatial_state sps1) (mk_spatial_state sps2) with
        | Ok inst -> Some inst
        | Error _ -> None)
      in
      let match_up_conj inst spss2 spss1 =
        List.fold_left (fun acc sps2 ->
          match acc with
          | Some (inst, spss1) ->
            find_map_res (match_up_conjunct inst sps2) spss1
          | None -> None)
          (Some (inst, spss1)) spss2
      in
      (match match_up_conj inst spss2 spss1 with
      | Some (inst, []) -> Some inst (* Only allow when spss1 and spss2 are same len. TODO?!?! *)
      | _ -> None)
    | _ -> None
  in
  (* Sort sps2 so that acc(v)/arr(v) where v is a var (i.e. like x.next) are in the end *)
  let sps2 =
    state2.spatial |> List.partition
      (function PointsTo (Var _, _) | Arr (Var _, _, _) -> false | _ -> true)
    |> (fun (x, y) -> x @ y)
  in
  match sps2 with
  | [] ->
    let st = {st with se_eqs = IdMap.union (fun _ -> failwith "") st.se_eqs inst} in
    (* Check if p2 is implied by p1 *)
    (match check_pure_entail st state1.pure state2.pure with
    | None ->
      Ok (state1.spatial, inst)
    | Some errs -> Error errs)
  | sp2 :: sps2' ->
    (match find_map_res (match_up_sp inst sp2) state1.spatial with
    | Some (inst, sps1') ->
        let state1' = { state1 with spatial = sps1' } in
        let state2' = subst_state inst { state2 with spatial = sps2' } in
        find_frame st ~inst:inst state1' state2'
    | None -> Error ([], Model.empty)) (* TODO get errors? *)

(** Returns [Ok inst] if [state1] |= [state2], else [Error (error messages)]. *)
and check_entailment st ?(inst=empty_eqs) state1 state2 =
  let st1 = simplify_state { st with se_state = state1 } in
  let eqs, state1 = st1.se_eqs, st1.se_state in
  let state2 =
    state2 |>
    apply_equalities eqs |>
    apply_equalities inst |>
    remove_useless_existentials
  in
  Debug.debug (fun () ->
    sprintf "\nChecking entailment:\n%s\n|=\n%s\n"
      (string_of_se_state st1) (string_of_state state2)
  );
  (* Check if find_frame returns empt *)
  match find_frame st ~inst:inst state1 state2 with
  | Ok ([], inst) -> Ok inst
  | Ok _ ->
    Error (["The frame was not empty for this entailment check"], Model.empty)
  | Error errs -> Error errs


(** Finds a call site for a function that's completely contained inside a conjunct.
  If found, [find_frame_conj p e state1 state2] returns a function [repl_fn] s.t.
  [repl_fn sm state2'] is the result of replacing [state2] inside [state1] with [state2'],
  and applying the substitution map [sm] on the remaining parts of [state1].
*)
let find_frame_conj st state1 state2 =
  let rec find_frame_inside_conj = function
    | [] -> Error ([], Model.empty)
    | sps :: spss ->
      (match find_frame st { state1 with spatial = sps } state2 with
      | Ok (frame, inst) ->
        let repl_fn = (fun sm foo_post ->
          let frame = List.map (subst_spatial_pred sm) frame in
          let spss = List.map (List.map (subst_spatial_pred sm)) spss in
          (foo_post @ frame) :: spss)
        in
        Ok (repl_fn, inst)
      | Error errs1 ->
        (match find_frame_inside_conj spss with
        | Ok (repl_fn, inst) ->
          let repl_fn = (fun sm foo_post ->
            let sps = List.map (subst_spatial_pred sm) sps in
            sps :: (repl_fn sm foo_post))
          in
          Ok (repl_fn, inst)
        | Error ([], _) -> Error errs1
        | Error errs -> Error errs))
  in
  let rec find_frame_conj = function
    | [] -> Error ([], Model.empty)
    | Conj spss :: spatial' ->
      (match find_frame_inside_conj spss with
      | Ok (repl_fn, inst) ->
        let repl_fn = (fun sm foo_post ->
          Conj (repl_fn sm foo_post) :: (List.map (subst_spatial_pred sm) spatial'))
        in
        Ok (repl_fn, inst)
      | Error errs ->
        (match find_frame_conj spatial' with
        | Ok (repl_fn, inst) ->
          let repl_fn =
            (fun sm foo_post ->
              let spss = List.map (List.map (subst_spatial_pred sm)) spss in
              Conj spss :: (repl_fn sm foo_post))
          in
          Ok (repl_fn, inst)
        | Error ([], _) -> Error errs
        | Error errs -> Error errs))
    | sp :: spatial' ->
      (match find_frame_conj spatial' with
      | Ok (repl_fn, inst) ->
        let repl_fn =
          (fun sm foo_post -> (subst_spatial_pred sm sp) :: (repl_fn sm foo_post))
        in
        Ok (repl_fn, inst)
      | Error errs -> Error errs)
  in
  find_frame_conj state1.spatial


(** Finds a call site for a function that's completely contained inside a dirty
  region.
  [state2] must have only PointsTo/Arr - no predicates allowed.*)
let find_frame_dirty st state1 state2 =
  let find_inside_dirty = function
    | sp -> Error ([], Model.empty)
  in
  (* Cycle through sp1 looking for a dirty that works, keeping seen stuff in sp1a *)
  let rec find_dirty sp1a = function
    | sp :: sp1b ->
      (match find_inside_dirty sp with
      | Error ([], m) -> find_dirty (sp :: sp1a) sp1b
      | Error (msgs, m) -> Error (msgs, m)
      | Ok (rf, inst) -> assert false)

    | [] -> Error ([], Model.empty)
  in
  match List.exists (function PointsTo _ | Arr _ -> false | _ -> true) state2.spatial with
  | true -> Error ([], Model.empty) (* Only PointsTos allowed *)
  | false -> find_dirty [] state1.spatial


(** Matches up arrays in pre and post of a function call and adds a pure formula to post
  that enforces that the lengths are the same. *)
let force_array_lengths_equal pre post =
  let length_axiom = 
    List.fold_left (fun acc -> function
        | Arr (a, l, m) ->
          let f =
            match List.find_opt (function Arr (a', l', _) -> a = a' | _ -> false) pre.spatial with
            | Some (Arr (_, l', _)) -> mk_eq l l'
            | _ -> mk_true
          in
          f :: acc
        | _ -> acc)
      [] post.spatial
  in
  strengthen_pure_state length_axiom post


(** Check that we have permission to the array, and that index is in bounds *)
let check_array_acc st arr idx =
  let state = st.se_state in
  match find_array arr state.spatial with
  | Some (l, _), _ ->
     let idx_in_bds = smk_and [(mk_leq (mk_int 0) idx); (mk_lt idx l)] in
     Debug.debug (fun () -> "\n\nChecking array index is in bounds:\n");
     (match check_pure_entail st state.pure idx_in_bds with
     | None -> ()
     | Some errs -> raise_err "Possible array index out of bounds error")
  | None, _ ->
    raise_err "Possible invalid array read"


(** Check that all array read terms in [t] are safe on state [st] *)
let check_array_reads st t =
  let rec check = function
    | Var _ as t -> t
    | App (Read, [a; idx], srt)
        (*| App (Read, [f; App (Read, [App (ArrayCells, [a], _); idx], _)], srt)*)
      when sort_of a = Loc (Array srt) ->
      (* Array reads *)
      let a, _ = eval_term_no_olds st.se_fields st.se_state a in
      let idx, _ = eval_term_no_olds st.se_fields st.se_state idx in
      check_array_acc st a idx;
      App (Read, [check a; check idx], srt)
    | App (s, ts, srt) -> App (s, List.map check ts, srt)
  in
  check t


(** Process term by substituting eqs, looking up field reads. *)
(* TODO: this is because assume/assert may have array reads under binders which have guards.
  So for now we are not checking them. Better way to do this? *)
let process_no_array st t =
  let t = subst_term st.se_eqs t in
  let t, state = eval_term_no_olds st.se_fields st.se_state t in
  t, {st with se_state = state}

(** Process term by substituting eqs, looking up field reads, and checking array reads. *)
let process st t =
  let t = t |> subst_term st.se_eqs |> check_array_reads st in
  let t, state = eval_term_no_olds st.se_fields st.se_state t in
  t, {st with se_state = state}


(** Symbolically execute commands [comms] on state [st] and check [postcond]. *)
let rec symb_exec st postcond comms =
  (* Some helpers *)
  let lookup_type id = (find_var st.se_prog st.se_proc id).var_sort in
  let mk_var_like srt id =
    let id' = fresh_ident (name id) in
    mk_free_const srt id'
  in
  let mk_var_like_id id = mk_var_like (lookup_type id) id in
  let mk_const_term id = mk_free_const (lookup_type id) id in
  let mk_error msg errs model pos =
    [(pos, String.concat "\n\n" (msg :: errs), model)]
  in
  let pos = match comms with
    | Basic (_, pp) :: _ -> pp.pp_pos
    | _ -> dummy_position
  in

  (* First, simplify_state the pre state *)
  let st = simplify_state st in

  (* If flag is set, check that current state isn't unsat *)
  if !Config.check_unsat then begin
    Debug.debug (fun () -> "Checking if current state is unsat:\n");
    let st' = add_neq_constraints st in
    try
      (match find_frame st st'.se_state (mk_pure_state mk_false) with
      | Ok _ ->
        print_endline @@ (string_of_src_pos pos) ^ "\nWarning: Intermediate state was unsat"
      | Error _ ->
        Debug.debug (fun () -> "State is satisfiable.\n"))
    with _ ->
      print_endline @@ (string_of_src_pos pos) ^ "\nWarning: unsat check hit exception"
  end;

  let se = function
  | [] ->
    Debug.debug (fun () ->
      sprintf "%sExecuting check postcondition: %s%sCurrent state:\n%s\n"
        lineSep (string_of_state postcond)
        lineSep (string_of_se_state st)
    );
    (* TODO do this better *)
    let st = add_neq_constraints st in
    (* First, check if current state is unsat *)
    (try
      (match find_frame st st.se_state (mk_pure_state mk_false) with
      | Ok _ -> (* Unsat, so forget checking postcondition *)
        []
      | Error _ ->
    (match check_entailment st st.se_state postcond with
      | Ok _ -> []
      | Error (errs, m) ->
      (* TODO to get line numbers, convert returns into asserts *)
            mk_error "A postcondition may not hold" errs m dummy_position))
    with _ ->
      print_endline @@ (string_of_src_pos pos) ^ "\nWarning: unsat check hit exception";
    (match check_entailment st st.se_state postcond with
      | Ok _ -> []
      | Error (errs, m) ->
      (* TODO to get line numbers, convert returns into asserts *)
            mk_error "A postcondition may not hold" errs m dummy_position))
  | (Basic (Assign {assign_lhs=[_];
                    assign_rhs=[App (Write, [arr; idx; rhs], Loc (Array _))]}, pp) as comm) :: comms' ->
  (*| (Basic (Assign {assign_lhs=[f];
        assign_rhs=[App (Write, [array_state;
                    App (Read, [App (ArrayCells, [arr], _); idx], _); rhs], srt)]}, pp)
        as comm) :: comms'
      when array_state = Grassifier.array_state true (sort_of rhs)
        || array_state = Grassifier.array_state false (sort_of rhs) ->*)
    Debug.debug (fun () ->
      sprintf "%sExecuting array write: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_se_state st)
    );
    let arr, st = process st arr in
    let idx, st = process st idx in
    let rhs, st = process st rhs in
    (* Check that we have permission to the array, and that index is in bounds *)
    check_array_acc st arr idx;
    (* Find the map for arr and bump it up *)
    (match find_array arr st.se_state.spatial with
    | Some (_, (App (FreeSym m_id, [], _) as m)), mk_spatial' ->
      let m' = mk_var_like (sort_of m) m_id in
      let sm = IdMap.singleton m_id m' in
      let idx, rhs = idx |> subst_term sm, rhs |> subst_term sm in
      let st = subst_se_state sm st in
      let pure = smk_and [mk_eq m (mk_write m' [idx] rhs); st.se_state.pure] in
      let st' = update_se_state st { pure = pure; spatial = mk_spatial' m } in
      symb_exec st' postcond comms'
    | Some _, _ -> failwith "Array map was not a const term"
    | None, _ ->
      [(pp.pp_pos, "Possible invalid array write", Model.empty)])
  | Basic (Assign {assign_lhs=[fld];
        assign_rhs=[App (Write, [App (FreeSym fld', [], _);
          loc; rhs], srt)]}, pp) as comm :: comms'
      when fld = fld' && IdSet.mem fld st.se_fields ->
    Debug.debug (fun () ->
      sprintf "%sExecuting mutate: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_se_state st)
    );
    (* First, process/check loc and rhs *)
    let loc, st = process st loc in
    let rhs, st = process st rhs in
    (* Find the node to mutate *)
    (match find_ptsto loc st.se_state.spatial with
    | Some fs, _, mk_spatial' ->
      (* mutate fs to fs' so that it contains (fld, rhs) *)
      let fs' =
        if List.exists (fst >> (=) fld) fs
        then List.map (fun (f, e) -> (f, if f = fld then rhs else e)) fs
        else (fld, rhs) :: fs
      in
      let st' = update_se_state st { pure = st.se_state.pure; spatial = mk_spatial' fs' } in
      symb_exec st' postcond comms'
    | None, _, _ ->
      [(pp.pp_pos, "Possible invalid heap mutation", Model.empty)])
  | Basic (Assign {assign_lhs=ids; assign_rhs=ts}, pp) as comm :: comms' ->
    Debug.debug (fun () ->
      sprintf "%sExecuting assignment: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_se_state st)
    );
    (* TODO simultaneous assignments can't touch heap, so do all at once *)
    let st =
      List.combine ids ts
      |> List.fold_left (fun st (id, rhs) ->
          (* First, substitute/eval/check rhs *)
          let rhs, st = process st rhs in
          let sm = IdMap.singleton id (mk_var_like_id id) in
          let rhs' = subst_term sm rhs in
          let st = subst_se_state sm st in
          let state' = add_state (mk_pure_state (mk_eq (mk_const_term id) rhs')) st.se_state in
          update_se_state st state'
        ) st
    in
    symb_exec st postcond comms'
  | Basic (Call {call_lhs=lhs; call_name=foo; call_args=args}, pp) as comm :: comms' ->
    Debug.debug (fun () ->
      sprintf "%sExecuting procedure call: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_se_state st)
    );
    (* First, substitute eqs and eval args *)
    let args, st = args |> fold_left_map process st in
    Debug.debug (fun () -> sprintf "\nOn args: %s\n" (string_of_format pr_term_list args));
    (* Look up pre/post of foo *)
    let c = (find_proc st.se_prog foo).proc_contract in
    let foo_pre, foo_post =
      let _, pre = c.contr_precond |> state_of_spec_list st.se_fields None  in
      let pre, post = c.contr_postcond |> state_of_spec_list st.se_fields (Some pre) in
      (* Since nothing can change array lengths, make them equal *)
      let post = force_array_lengths_equal pre post in
      remove_useless_existentials pre, remove_useless_existentials post
    in
    let foo_pre =
      (* Substitute formal params -> actual params in foo_pre/post *)
      foo_pre |> subst_state (mk_eqs c.contr_formals args)
    in
    (* Replace lhs vars with fresh vars. For every part of new state *)
    let sm =
      lhs |> List.fold_left (fun sm id ->
          IdMap.add id (mk_var_like_id id) sm)
        IdMap.empty
    in
    (* Substitute formal params -> actual params & return vars -> lhs vars in foo_post *)
    let foo_post =
      (* args will be part of foo_post, so substitute here too *)
      let args = List.map (subst_term sm) args in
      let sm = mk_eqs c.contr_formals args in
      let sm = List.fold_left2 (fun sm r l -> IdMap.add r (mk_const_term l) sm)
        sm c.contr_returns lhs
      in
      foo_post |> subst_state sm
    in
    (* Add derived equalities before checking for frame & entailment *)
    (* TODO do this by keeping disequalities in state? *)
    let st = add_neq_constraints st in
    let foo_pre = apply_equalities st.se_eqs foo_pre in
    Debug.debug (fun () ->
      sprintf "\nPrecondition:\n%s\n\nPostcondition:\n%s\n"
        (string_of_state foo_pre) (string_of_state foo_post)
    );
    let repl_fn =
      match find_frame st st.se_state foo_pre with
        | Ok (frame, inst) ->
          let frame = List.map (subst_spatial_pred sm) frame in
          Ok ((fun sm foo_post -> foo_post @ frame), inst)
        | Error ([], m) ->
          (match find_frame_dirty st st.se_state foo_pre with
          | Error ([], m) ->
            (* Try to see if a lemma can be applied inside a conjunct *)
            if (find_proc st.se_prog foo).proc_is_lemma then
              find_frame_conj st st.se_state foo_pre
            else Error ([], m)
          | e -> e)
        | Error (msgs, m) as e -> e
    in
    (* Then, create vars for old vals of all x in lhs, and substitute in eqs & frame *)
    (match repl_fn with
      | Ok (repl_fn, inst) ->
      let eqs = subst_eqs sm st.se_eqs in
      let pure = st.se_state.pure |> subst_form sm in
      let state = { pure = smk_and [pure; foo_post.pure]; spatial = repl_fn sm foo_post.spatial } in
      (* This is to apply equalities derived during frame inference *)
      let state = subst_state inst state in
      symb_exec {st with se_eqs = eqs; se_state = state} postcond comms'
      | Error (errs, m) ->
        mk_error "The precondition of this procedure call may not hold" errs m pp.pp_pos)
  | Seq (comms, _) :: comms' ->
    symb_exec st postcond (comms @ comms')
  | Basic (Havoc {havoc_args=vars}, pp) as comm :: comms' ->
    (* Just substitute all occurrances of v for new var v' in symbolic state *)
    Debug.debug (fun () ->
      sprintf "%sExecuting havoc: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_se_state st)
    );
    let sm =
      List.fold_left (fun sm v -> IdMap.add v (mk_var_like_id v) sm)
        IdMap.empty vars
    in
    let st = subst_se_state sm st in
    symb_exec st postcond comms'
  | Basic (Assume {spec_form=FOL spec}, pp) as comm :: comms' ->
    (* Pure assume statements are just added to pure part of state *)
    Debug.debug (fun () ->
      sprintf "%sExecuting assume: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_se_state st)
    );
    let spec, st = fold_map_terms process_no_array st spec in
    symb_exec {st with se_state = add_state (mk_pure_state spec) st.se_state} postcond comms'
  | Choice (comms, _) :: comms' ->
    List.fold_left (fun errors comm ->
        match errors with
        | [] ->
          symb_exec st postcond (comm :: comms')
        | _ -> errors)
      [] comms
  | Basic (Assert spec, pp) as comm :: comms' ->
    Debug.debug (fun () ->
      sprintf "%sExecuting assert: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_se_state st)
    );
    (match spec.spec_form with
    | SL _ ->
      let _, spec_st = state_of_spec_list st.se_fields None [spec] in
      let st' = add_neq_constraints st in
      (match check_entailment st st'.se_state spec_st with
        | Ok _ ->
        symb_exec st postcond comms'
        | Error (errs, m) -> mk_error "This assertion may not hold" errs m pp.pp_pos)
    | FOL spec_form ->
      let spec, st = fold_map_terms process_no_array st spec_form in
      let st' = add_neq_constraints st in
      (match find_frame st st'.se_state (mk_pure_state spec) with
        | Ok _ ->
        symb_exec {st with se_state = add_state (mk_pure_state spec) st.se_state} postcond comms'
        | Error (errs, m) -> mk_error "This assertion may not hold" errs m pp.pp_pos))
  | Basic (Return {return_args=xs}, pp) as comm :: _ ->
    Debug.debug (fun () ->
      sprintf "%sExecuting return: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_se_state st)
    );
    (* Substitute xs for return vars in postcond and throw away rest of comms *)
    let xs, st = fold_left_map process st xs in
    let ret_vars = st.se_proc.proc_contract.contr_returns in
    let sm =
      List.combine ret_vars xs
      |> List.fold_left (fun sm (v, x) -> IdMap.add v x sm) IdMap.empty in
    let postcond = subst_state sm postcond in
    symb_exec st postcond []
  | Basic (Split spec, pp) as comm :: comms' ->
    Debug.debug (fun () ->
      sprintf "%sExecuting split: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_se_state st)
    );
    (* First assert the spec, then assume spec as new state *)
    let _, spec_st = state_of_spec_list st.se_fields None [spec] in
    let st' = add_neq_constraints st in
    (match check_entailment st st'.se_state spec_st with
    | Ok _ ->
        symb_exec {st with se_eqs = empty_eqs; se_state = spec_st} postcond comms'
    | Error (errs, m) -> mk_error "This split may not hold" errs m pp.pp_pos)
  | Basic (New {new_lhs=id; new_sort=srt; new_args=ts}, pp) as comm :: comms' ->
      Debug.debug
        (fun () ->
          sprintf "%sExecuting new command: %d: %s%sCurrent state:\n%s\n"
            lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
            lineSep (string_of_se_state st)
        );
      let sm = IdMap.singleton id (mk_var_like_id id) in
      let vts = List.map (fun t -> fresh_const (sort_of t)) ts in
      let st =
      List.combine vts ts
      |> List.fold_left (fun st (v, t) ->
          (* First, eval/check t *)
          let t, st = process st t in
          let t' = subst_term sm t in
          {st with se_state = add_state (mk_pure_state (mk_eq v t')) st.se_state}
        ) st
      in
      let st = subst_se_state sm st in
      let new_cell = match srt with
      | Loc (FreeSrt _) -> PointsTo (mk_const_term id, [])
      | Loc (Array srt) ->
          let m = fresh_const (Map ([Int], srt)) in
          let l = List.hd vts in
          let length_ok = mk_leq (mk_int 0) l in
          Debug.debug (fun () -> "\n\nChecking that array length is nonnegative:\n");
          (match check_pure_entail st (st.se_state.pure) length_ok with
          | None -> ()
          | Some errs -> raise_err "Possibly attempting to create an array of negative length");
          Arr (mk_const_term id, List.hd vts, m)
      | _ -> failwith "unexpected new command"
      in
      let st = {st with se_state = add_state (mk_spatial_state [new_cell]) st.se_state} in
      symb_exec st postcond comms'
  | Basic (Assume _, _) :: _ -> failwith "TODO Assume SL command"
  | Basic (Dispose _, _) :: _ -> failwith "TODO Dispose command"
  | Loop _ :: _ -> failwith "TODO Loop command"
  in
  try
    se comms
  with SymbExecFail msg ->
    mk_error msg [] Model.empty pos


(** Check procedure [proc] in program [prog] using symbolic execution. *)
(* TODO: take care of aux_axioms *)
let check spl_prog prog aux_axioms proc =
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
  (* Make sure FOL predicates are not of the form SL (Pure fol_formula)) *)
  let prog = prog |>
    map_preds (fun pred ->
      {pred with pred_body =
        pred.pred_body
        |> Opt.map (fun spec -> {spec with spec_form =
          match spec.spec_form with
          | SL (Sl.Pure (f, pos)) -> FOL f
          | f -> f }
        )}
    )
  in
  let errors = match proc.proc_body with
  | Some comm ->
    let pre =
      try
        Ok (state_of_spec_list flds None proc.proc_contract.contr_precond |> snd)
      with SymbExecFail msg ->
        Error [(proc.proc_contract.contr_pos, "In precondition: " ^ msg, Model.empty)]
    in
    (match pre with
    | Ok pre ->
      let prepost =
        try
          Ok (state_of_spec_list flds (Some pre) proc.proc_contract.contr_postcond)
        with SymbExecFail msg ->
          Error [(proc.proc_contract.contr_pos, "In postcondition: " ^ msg, Model.empty)]
      in
      (match prepost with
      | Ok (pre, post) ->
        Debug.debug (fun () ->
          sprintf "\nPrecondition:\n%s\n\nPostcondition:\n%s\n"
            (string_of_state pre) (string_of_state post)
        );
        let st =
          {se_state = pre; se_prog = prog; se_proc = proc;
           se_fields = flds; se_eqs = empty_eqs}
        in
        symb_exec st post [comm]
      | Error errs -> errs)
    | Error errs -> errs)
  | None ->
    []
  in aux_axioms, errors

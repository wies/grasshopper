(** {5 Symbolic execution based verifier} *)

open Util
open Grass
open GrassUtil
open Prog
open Printf

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
  | Dirty of spatial_pred list * term list  (** Dirty region: [f1 * ..]_(e1, ..) *)
  | Conj of spatial_pred list list  (** Conjunction of spatial states *)

(** A symbolic state is a (pure formula, a list of spatial predicates).
  Note: program vars are represented as FreeSymb constants,
  existential vars are represented as Var variables.
 *)
type state = form * spatial_pred list
(* TODO also add prog, flds, eqs, etc to state *)

(** Equalities derived so far in the symbolic execution, as a map: ident -> term,
  kept so that they can be substituted into the command and the post.
  Invariant: if map is {x1: E1, ...} then xi are distinct and xi is not in Ej for i != j.
  ASSUMES: vars and constants do not share names!
  TODO: can we make it ident IdMap.t now?
  *)
type equalities = term IdMap.t


let empty_state = (mk_true, [])

let empty_eqs = IdMap.empty


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
  | Dirty (fs, ts) ->
    sprintf "[%s](%s)" (string_of_spatial_pred_list fs) (ts |> List.map string_of_term |> String.concat ", ")
  | Conj fss ->
    List.map (function
        | [p] -> string_of_spatial_pred p
        | ps -> "(" ^ string_of_spatial_pred_list ps ^ ")"
      ) fss
    |> String.concat " && "

and string_of_spatial_pred_list sps =
  sps |> List.map string_of_spatial_pred |> String.concat " * "

let string_of_state ((pure, spatial): state) =
  let spatial =
    match spatial with
    | [] -> "emp"
    | spatial -> string_of_spatial_pred_list spatial
  in
  let pure = pure
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

let string_of_eqs_state eqs state =
  sprintf "Eqs: %s\n%s" (string_of_equalities eqs) (string_of_state state)


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
  | Dirty (f, ts) as sp :: spatial' ->
    (match find_ptsto loc f with
    | Some fs, repl_fn_rd, repl_fn_wr  ->
      let repl_fn_rd = (fun fs' -> Dirty (repl_fn_rd fs', ts) :: spatial') in
      let repl_fn_wr = (fun fs' -> Dirty (repl_fn_wr fs', ts) :: spatial') in
      Some fs, repl_fn_rd, repl_fn_wr
    | None, _, _ ->
      let res, repl_fn_rd, repl_fn_wr = find_ptsto loc spatial' in
      res, (fun fs' -> sp :: repl_fn_rd fs'), (fun fs' -> sp :: repl_fn_wr fs')
    )
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
  | Dirty (f, ts) as sp :: spatial' ->
    (match find_array loc f with
    | Some lm, repl_fn_wr  ->
      let repl_fn_wr = (fun fs' -> Dirty (repl_fn_wr fs', ts) :: spatial') in
      Some lm, repl_fn_wr
    | None, _ ->
      let res, repl_fn_wr = find_array loc spatial' in
      res, (fun fs' -> sp :: repl_fn_wr fs')
    )
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
let rec eval_term fields (old_state, state, spatial') = function
  | Var _ as t -> t, (old_state, state, spatial')
  | App (Read, [App (FreeSym fld, [], _); loc], srt)
      when IdSet.mem fld fields -> (* Field reads *)
    let loc, (old_state, state, spatial') = eval_term fields (old_state, state, spatial') loc in
    (match find_ptsto loc (snd state) with
    | Some fs, mk_spatial, _ ->
      (* lookup fld in fs, so that loc |-> fs' and (fld, e) is in fs' *)
      let e, fs' =
        try List.assoc fld fs, fs
        with Not_found -> let e = fresh_const srt in e, (fld, e) :: fs
      in
      let spatial = mk_spatial fs' in
      e, (old_state, (fst state, spatial), spatial')
    | None, _, _ ->
      (match find_ptsto_spatial' loc spatial' with
      | Some (fs, spatial') -> 
        (* lookup fld in fs, so that loc |-> fs' and (fld, e) is in fs' *)
        let e, fs' =
          try List.assoc fld fs, fs
          with Not_found -> let e = fresh_const srt in e, (fld, e) :: fs
        in
        e, (old_state, state, PointsTo (loc, fs') :: spatial')
      | None -> (* Add loc to spatial' to indicate we need an acc(loc) in the future *)
        let e = fresh_const srt in
        e, (old_state, state, PointsTo (loc, [fld, e]) :: spatial')))
  | App (Read, [f; a; idx], srt)
  | App (Read, [f; App (Read, [App (ArrayCells, [a], _); idx], _)], srt)
      when f = (Grassifier.array_state true srt) || f = (Grassifier.array_state false srt) ->
    (* Array reads *)
    let a, (old_state, state, spatial') = eval_term fields (old_state, state, spatial') a in
    let idx, (old_state, state, spatial') = eval_term fields (old_state, state, spatial') idx in
    let m, spatial' =
    (match find_array a (snd state) with
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
    (match find_array a (snd state) with
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
  | App (Write, _, _) as t ->
    failwith @@ "eval_term called on write " ^ (string_of_term t)
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
  let add (pure, spatial) (pure', spatial') =
    (smk_and [pure; pure'], spatial @ spatial')
  in
  (* [spatial'] is a list of outstanding spatial_preds needed to eval [state] *)
  let convert_form (old_state, state, spatial') f =
    let f, (old_state, state, spatial') =
      fold_map_terms eval_term (old_state, state, spatial') f
    in
    (old_state, add (f, []) state, spatial')
  in
  let rec convert_sl_form (old_state, state, spatial') f =
    let fail () = failwith @@ "Unsupported formula " ^ (Sl.string_of_form f) in
    match f with
    | Sl.Pure (f, _) -> convert_form (old_state, state, spatial') f
    | Sl.Atom (Sl.Emp, ts, _) -> old_state, state, spatial'
    | Sl.Atom (Sl.Region, [(App (SetEnum, [x], Set Loc Array srt))], _) -> (* arr(x) *)
      let x, (old_state, state, spatial') = eval_term (old_state, state, spatial') x in
      (* First check if we've already created it in spatial' *)
      let sp, l, spatial' =
        (match find_arr_spatial' x spatial' with
        | Some ((l, m), spatial') ->
          Arr (x, l, m), l, spatial'
        | None ->
          let l = fresh_array_length () in
          let m = fresh_array_map srt in
          Arr (x, l, m), l, spatial')
      in
      let len_axiom = mk_leq (mk_int 0) l in
      old_state, add (len_axiom, [sp]) state, spatial'
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
      let pures, spatials = List.split conj_states in
      let spatials = List.filter (function [] -> false | _ -> true) spatials in
      (match spatials with
      | [] -> old_state, add (smk_and pures, []) state, spatial'
      | _ -> old_state, add (smk_and pures, [Conj spatials]) state, spatial')
    | Sl.BoolOp _ -> fail ()
    | Sl.Binder (b, vs, f, _) ->
      let pure, spatial = state in
      let old_state, (pure1, spatial1), spatial' =
        convert_sl_form (old_state, (mk_true, spatial), spatial') f
      in
      if spatial1 = spatial then
        old_state, add (smk_binder b vs pure1, []) (pure, spatial), spatial'
      else
        failwith @@ "Confused by spatial under binder: " ^ (Sl.string_of_form f)
    | Sl.Dirty (f, ts, _) ->
      let old_state, (pure1, spatial1), spatial' =
        convert_sl_form (old_state, empty_state, spatial') f
      in
      old_state, add (pure1, [Dirty (spatial1, ts)]) state, spatial'
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
  | Dirty (sps, ts) ->
    Dirty (List.map (subst_spatial_pred sm) sps, List.map (subst_term sm) ts)
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

(** Normalize a Conj by some kind of sorting *)
let sort_conj = function
  | Conj spss ->
    Conj (spss |> List.map (List.stable_sort compare) |> List.stable_sort compare)
  | sp -> sp

(** Find equalities of the form const == const in [pure] and add to [eqs] *)
let find_equalities eqs (pure: form) =
  let rec find_eq sm = function
    | Atom (App (Eq, [(App (FreeSym id, [],  _)); App (FreeSym _, [],  _) as t2], _), _) ->
      add_eq id t2 sm
    | BoolOp (And, fs) ->
      List.fold_left find_eq sm fs
    | Binder (_, [], f, _) -> find_eq sm f
    | _ -> sm
  in
  find_eq eqs pure

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
  let (pure, spatial) = subst_state eqs state in
  remove_trivial_equalities pure, spatial

let remove_useless_existentials ((pure, spatial) as state : state) : state =
  (* Note: can also use GrassUtil.foralls_to_exists for this *)
  apply_equalities (find_var_equalities pure) state

(** Kill useless existential vars in [state], find equalities between constants,
  add to [eqs] and simplify. *)
let simplify eqs (pure, spatial) =
  let (pure, spatial) = remove_useless_existentials (pure |> nnf, spatial) in
  let eqs = find_equalities eqs pure in
  eqs, apply_equalities eqs (pure, spatial)

(** Add implicit disequalities from spatial to pure. Assumes normalized by eq. *)
let add_neq_constraints (pure, spatial) =
  let rec f acc locs = function
    | PointsTo (x, _) :: sps | Arr (x, _, _) :: sps ->
      let acc1 = TermSet.fold (fun y acc ->
          if sort_of x = sort_of y then mk_neq x y :: acc else acc)
        locs acc 
      in
      f acc1 (TermSet.add x locs) sps
    | Dirty (sp', _) :: sps ->
      let acc, locs = f acc locs sp' in
      f acc locs sps
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
  (smk_and (pure :: neqs), spatial)


(** ----------- Symbolic Execution ---------- *)


(* Returns None if the entailment holds, otherwise Some (list of error messages, model) *)
let check_pure_entail prog eqs p1 p2 =
  let (p2, _) = apply_equalities eqs (p2, []) in
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
        prog.prog_axioms
      |> List.map (subst_form eqs) (* Apply equalities in eqs *)
    in
    let p2 = Verifier.annotate_aux_msg "Related location" p2 in
    (* Close the formulas: assuming all free variables are existential *)
    let close f = smk_exists (IdSrtSet.elements (sorted_free_vars f)) f in
    let labels, f =
      smk_and [p1; mk_not p2] |> close |> nnf
      (* Add definitions of all referenced predicates and functions *)
      |> Verifier.add_pred_insts prog
      (* Add axioms *)
      |> (fun f -> smk_and (f :: axioms))
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
let rec find_frame prog ?(inst=empty_eqs) eqs (p1, sps1) (p2, sps2) =
  Debug.debugl 1 (fun () ->
    sprintf "\nFinding frame with %s for:\n%s\n|=\n%s &*& ??\n"
      (string_of_equalities inst)
      (string_of_spatial_pred_list sps1) (string_of_spatial_pred_list sps2)
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
    | Dirty (sp2a, ts), Dirty (sp1a, ts') when ts = ts' ->
      (match check_entailment prog ~inst:inst eqs (mk_true, sp1a) (mk_true, sp2a) with
      | Ok inst -> Some inst
      | Error _ -> None)
    | Conj spss2, Conj spss1 ->
      let match_up_conjunct inst sps2 sps1 =
        (match check_entailment prog ~inst:inst eqs (mk_true, sps1) (mk_true, sps2) with
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
  match sps2 with
  | [] ->
    (* Check if p2 is implied by p1 *)
    (match check_pure_entail prog (IdMap.union (fun _ -> failwith "") eqs inst) p1 p2 with
    | None ->
      Ok (sps1, inst)
    | Some errs -> Error errs)
  | sp2 :: sps2' ->
    (match find_map_res (match_up_sp inst sp2) sps1 with
    | Some (inst, sps1') ->
      let p2, sps2 = subst_state inst (p2, sps2') in
      find_frame prog ~inst:inst eqs (p1, sps1') (p2, sps2)
    | None -> Error ([], Model.empty)) (* TODO get errors? *)

(** Returns [Ok inst] if [(p1, sp1)] |= [(p2, sp2)], else Error (error messages). *)
and check_entailment prog ?(inst=empty_eqs) eqs (p1, sp1) (p2, sp2) =
  let eqs, (p1, sp1) = simplify eqs (p1, sp1) in
  let (p2, sp2) =
    (p2, sp2)
    |> apply_equalities eqs |> apply_equalities inst |> remove_useless_existentials
  in
  Debug.debug (fun () ->
    sprintf "\nChecking entailment:\n%s\n|=\n%s\n"
      (string_of_eqs_state eqs (p1, sp1)) (string_of_state (p2, sp2))
  );
  (* Check if find_frame returns empt *)
  match find_frame ~inst:inst prog eqs (p1, sp1) (p2, sp2) with
  | Ok ([], inst) -> Ok inst
  | Ok _ ->
    Error (["The frame was not empty for this entailment check"], Model.empty)
  | Error errs -> Error errs


(** Finds a call site for a function that's completely contained inside a conjunct.
  If found, [find_frame_conj p e state1 state2] returns a function [repl_fn] s.t.
  [repl_fn sm state2'] is the result of replacing [state2] inside [state1] with [state2'],
  and applying the substitution map [sm] on the remaining parts of [state1].
*)
let find_frame_conj prog eqs (pure, spatial) state2 =
  let rec find_frame_inside_conj = function
    | [] -> Error ([], Model.empty)
    | sps :: spss ->
      (match find_frame prog eqs (pure, sps) state2 with
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
  find_frame_conj spatial


(** Finds a call site for a function that's completely contained inside a dirty
  region.
  [state2] must have only PointsTos - no predicates allowed.*)
let find_frame_dirty prog eqs (p1, sp1) (p2, sp2) =
  let find_inside_dirty = function
    | Dirty (sp1a, ts) ->
      (match find_frame prog eqs (p1, sp1a) (p2, sp2) with
      | Ok (fr, inst) ->
        let repl_fn sm post =
          Dirty ((List.map (subst_spatial_pred sm) fr) @ post, ts)
        in
        Ok (repl_fn, inst)
      | Error (msgs, m) -> Error (msgs, m))
    | sp -> Error ([], Model.empty)
  in
  (* Cycle through sp1 looking for a dirty that works, keeping seen stuff in sp1a *)
  let rec find_dirty sp1a = function
    | sp :: sp1b ->
      (match find_inside_dirty sp with
      | Ok (rf, inst) ->
        let repl_fn sm post =
          (rf sm post) :: (List.map (subst_spatial_pred sm) (sp1a @ sp1b))
        in
        Ok (repl_fn, inst)
      | Error ([], m) -> find_dirty (sp :: sp1a) sp1b
      | Error (msgs, m) -> Error (msgs, m))
    | [] -> Error ([], Model.empty)
  in
  match List.exists (function PointsTo _ -> false | _ -> true) sp2 with
  | true -> Error ([], Model.empty) (* Only PointsTos allowed *)
  | false -> find_dirty [] sp1


(** Check that we have permission to the array, and that index is in bounds *)
let check_array_acc prog eqs (pure, spatial) arr idx =
  match find_array arr spatial with
  | Some (l, _), _ ->
     let idx_in_bds = smk_and [(mk_leq (mk_int 0) idx); (mk_lt idx l)] in
     Debug.debug (fun () -> "\n\nChecking array index is in bounds:\n");
     (match check_pure_entail prog eqs pure idx_in_bds with
     | None -> ()
     | Some errs -> raise_err "Possible array index out of bounds error")
  | None, _ ->
    raise_err "Possible invalid array read"


(** Check that all array read terms in [t] are safe on state [state] *)
let check_array_reads prog eqs state t =
  let rec check = function
    | Var _ as t -> t
    | App (Read, [f; a; idx], srt) when f = (Grassifier.array_state true srt) ->
       (* Array reads *)
      check_array_acc prog eqs state a idx;
         App (Read, [f; check a; check idx], srt)
    | App (s, ts, srt) -> App (s, List.map check ts, srt)
  in
  (check t, state)


(** Process term by substituting eqs, looking up field reads. *)
(* TODO: this is because assume/assert may have array reads under binders which have guards.
  So for now we are not checking them. Better way to do this? *)
let process_no_array prog fields eqs state =
  subst_term eqs
  >> eval_term_no_olds fields state

(** Process term by substituting eqs, looking up field reads, and checking array reads. *)
let process prog fields eqs state =
  subst_term eqs
  >> check_array_reads prog eqs state
  >> (fun (t, state) -> eval_term_no_olds fields state t)


(** Symbolically execute command [comm] on state [state] and check [postcond]. *)
let rec symb_exec prog flds proc (eqs, state) postcond comms =
  (* Some helpers *)
  let lookup_type id = (find_var prog proc id).var_sort in
  let mk_var_like id =
    let id' = fresh_ident (name id) in
    mk_free_const (lookup_type id) id'
  in
  let mk_const_term id = mk_free_const (lookup_type id) id in
  let mk_error msg errs model pos =
    [(pos, String.concat "\n\n" (msg :: errs), model)]
  in
  let pos = match comms with
    | Basic (_, pp) :: _ -> pp.pp_pos
    | _ -> dummy_position
  in

  (* First, simplify the pre state *)
  let eqs, state = simplify eqs state in

  (* If flag is set, check that current state isn't unsat *)
  if !Config.check_unsat then begin
    Debug.debug (fun () -> "Checking if current state is unsat:\n");
    let state' = add_neq_constraints state in
    try
      (match find_frame prog eqs state' (mk_false, []) with
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
      sprintf "%sExecuting check postcondition: %s%s\n"
        lineSep (string_of_state postcond) lineSep);
    (* TODO do this better *)
    let state = add_neq_constraints state in
    (match check_entailment prog eqs state postcond with
      | Ok _ -> []
      | Error (errs, m) ->
      (* TODO to get line numbers, convert returns into asserts *)
        mk_error "A postcondition may not hold" errs m dummy_position)
  | Basic (Assign {assign_lhs=[fld];
        assign_rhs=[App (Write, [App (FreeSym fld', [], _);
          loc; rhs], srt)]}, pp) as comm :: comms'
      when fld = fld' ->
    Debug.debug (fun () ->
      sprintf "%sExecuting mutate: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_eqs_state eqs state)
    );
    (* First, process/check loc and rhs *)
    let loc, state = process prog flds eqs state loc in
    let rhs, (pure, spatial) = process prog flds eqs state rhs in
    (* Find the node to mutate *)
    (match find_ptsto loc spatial with
    | Some fs, _, mk_spatial' ->
      (* mutate fs to fs' so that it contains (fld, rhs) *)
      let fs' =
        if List.exists (fst >> (=) fld) fs
        then List.map (fun (f, e) -> (f, if f = fld then rhs else e)) fs
        else (fld, rhs) :: fs
      in
      symb_exec prog flds proc (eqs, (pure, mk_spatial' fs')) postcond comms'
    | None, _, _ ->
      [(pp.pp_pos, "Possible invalid heap mutation", Model.empty)])
  | Basic (Assign {assign_lhs=[f];
        assign_rhs=[App (Write, [array_state; arr; idx; rhs], srt)]}, pp) as comm :: comms'
      when array_state = Grassifier.array_state true (sort_of rhs) ->
    Debug.debug (fun () ->
      sprintf "%sExecuting array write: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_eqs_state eqs state)
    );
    let arr, state = process prog flds eqs state arr in
    let idx, state = process prog flds eqs state idx in
    let rhs, (pure, spatial) = process prog flds eqs state rhs in
    (* Check that we have permission to the array, and that index is in bounds *)
      check_array_acc prog eqs (pure, spatial) arr idx;
    (* Find the map for arr and bump it up *)
    (match find_array arr spatial with
    | Some (_, (App (FreeSym m_id, [], _) as m)), mk_spatial' ->
      let m' = mk_free_const (sort_of m) m_id in
      let pure = smk_and [mk_eq m (mk_write m' [idx] rhs); pure] in
      symb_exec prog flds proc (eqs, (pure, spatial)) postcond comms'
    | Some _, _ -> failwith "Array map was not a const term"
    | None, _ ->
      [(pp.pp_pos, "Possible invalid heap mutation", Model.empty)])
  | Basic (Assign {assign_lhs=ids; assign_rhs=ts}, pp) as comm :: comms' ->
    Debug.debug (fun () ->
      sprintf "%sExecuting assignment: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_eqs_state eqs state)
    );
    (* TODO simultaneous assignments can't touch heap, so do all at once *)
    let (eqs', state', postcond) =
      List.combine ids ts
      |> List.fold_left (fun (eqs, state, postcond) (id, rhs) ->
          (* First, substitute/eval/check rhs *)
          let rhs, state = process prog flds eqs state rhs in
          let sm = IdMap.singleton id (mk_var_like id) in
          let rhs' = subst_term sm rhs in
          let (pure, spatial) = subst_state sm state in
          (* let postcond = subst_state sm postcond in *)
          let eqs = subst_eqs sm eqs in
          eqs, (smk_and [(mk_eq (mk_const_term id) rhs'); pure], spatial), postcond
        ) (eqs, state, postcond)
    in
    symb_exec prog flds proc (eqs', state') postcond comms'
  | Basic (Call {call_lhs=lhs; call_name=foo; call_args=args}, pp) as comm :: comms' ->
    Debug.debug (fun () ->
      sprintf "%sExecuting function call: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_eqs_state eqs state)
    );
    (* First, substitute eqs and eval args *)
    let args, state = args
      |> fold_left_map (process prog flds eqs) state
    in
    Debug.debug (fun () -> sprintf "\nOn args: %s\n" (string_of_format pr_term_list args));
    (* Look up pre/post of foo *)
    let c = (find_proc prog foo).proc_contract in
    let foo_pre, foo_post =
      let _, pre = c.contr_precond |> state_of_spec_list flds None  in
      let pre, post = c.contr_postcond |> state_of_spec_list flds (Some pre) in
      remove_useless_existentials pre, remove_useless_existentials post
    in
    let foo_pre =
      (* Substitute formal params -> actual params in foo_pre/post *)
      foo_pre |> subst_state (mk_eqs c.contr_formals args)
    in
    (* Replace lhs vars with fresh vars. For every part of new state *)
    let sm =
      lhs |> List.fold_left (fun sm id ->
          IdMap.add id (mk_var_like id) sm)
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
    let state = add_neq_constraints state in
    let foo_pre = apply_equalities eqs foo_pre in
    Debug.debug (fun () ->
      sprintf "\nPrecondition:\n%s\n\nPostcondition:\n%s\n"
        (string_of_state foo_pre) (string_of_state foo_post)
    );
    let repl_fn =
      match find_frame prog eqs state foo_pre with
        | Ok (frame, inst) ->
          let frame = List.map (subst_spatial_pred sm) frame in
          Ok ((fun sm foo_post -> foo_post @ frame), inst)
        | Error ([], m) ->
          (match find_frame_dirty prog eqs state foo_pre with
          | Error ([], m) ->
            (* Try to see if a lemma can be applied inside a conjunct *)
            if (find_proc prog foo).proc_is_lemma then
              find_frame_conj prog eqs state foo_pre
            else Error ([], m)
          | e -> e)
        | Error (msgs, m) as e -> e
    in
    (* Then, create vars for old vals of all x in lhs, and substitute in eqs & frame *)
    (match repl_fn with
      | Ok (repl_fn, inst) ->
      let eqs = subst_eqs sm eqs in
      let pure = state |> fst |> subst_form sm in
      let (post_pure, post_spatial) = foo_post in
      let state = (smk_and [pure; post_pure], repl_fn sm post_spatial) in
      (* This is to apply equalities derived during frame inference *)
      let state = subst_state inst state in
      symb_exec prog flds proc (eqs, state) postcond comms'
      | Error (errs, m) ->
        mk_error "The precondition of this function call may not hold" errs m pp.pp_pos)
  | Seq (comms, _) :: comms' ->
    symb_exec prog flds proc (eqs, state) postcond (comms @ comms')
  | Basic (Havoc {havoc_args=vars}, pp) as comm :: comms' ->
    (* Just substitute all occurrances of v for new var v' in symbolic state *)
    Debug.debug (fun () ->
      sprintf "%sExecuting havoc: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_eqs_state eqs state)
    );
    let sm =
      List.fold_left (fun sm v -> IdMap.add v (mk_var_like v) sm)
        IdMap.empty vars
    in
    let eqs', state' = (subst_eqs sm eqs, subst_state sm state) in
    symb_exec prog flds proc (eqs', state') postcond comms'
  | Basic (Assume {spec_form=FOL spec}, pp) as comm :: comms' ->
    (* Pure assume statements are just added to pure part of state *)
    Debug.debug (fun () ->
      sprintf "%sExecuting assume: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_eqs_state eqs state)
    );
    let spec, (pure, spatial) = fold_map_terms (process_no_array prog flds eqs) state spec in
    symb_exec prog flds proc (eqs, (smk_and [pure; spec], spatial)) postcond comms'
  | Choice (comms, _) :: comms' ->
    List.fold_left (fun errors comm ->
        match errors with
        | [] ->
          symb_exec prog flds proc (eqs, state) postcond (comm :: comms')
        | _ -> errors)
      [] comms
  | Basic (Assert spec, pp) as comm :: comms' ->
    Debug.debug (fun () ->
      sprintf "%sExecuting assert: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_eqs_state eqs state)
    );
    (match spec.spec_form with
    | SL _ ->
      let _, spec_st = state_of_spec_list flds None [spec] in
      let state' = add_neq_constraints state in
      (match check_entailment prog eqs state' spec_st with
        | Ok _ ->
        symb_exec prog flds proc (eqs, state) postcond comms'
        | Error (errs, m) -> mk_error "This assert may not hold" errs m pp.pp_pos)
    | FOL spec_form ->
      let spec_form, state =
        fold_map_terms (process_no_array prog flds eqs) state spec_form
      in
      let state' = add_neq_constraints state in
      (match find_frame prog eqs state' (spec_form, []) with
        | Ok _ ->
        symb_exec prog flds proc (eqs, state) postcond comms'
        | Error (errs, m) -> mk_error "This assert may not hold" errs m pp.pp_pos))
  | Basic (Return {return_args=xs}, pp) as comm :: _ ->
    Debug.debug (fun () ->
      sprintf "%sExecuting return: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_eqs_state eqs state)
    );
    (* Substitute xs for return vars in postcond and throw away rest of comms *)
    let xs, state = fold_left_map (process prog flds eqs) state xs in
    let ret_vars = proc.proc_contract.contr_returns in
    let sm =
      List.combine ret_vars xs
      |> List.fold_left (fun sm (v, x) -> IdMap.add v x sm) IdMap.empty in
    let postcond = subst_state sm postcond in
    symb_exec prog flds proc (eqs, state) postcond []
  | Basic (Split spec, pp) as comm :: comms' ->
    Debug.debug (fun () ->
      sprintf "%sExecuting split: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_eqs_state eqs state)
    );
    (* First assert the spec, then assume spec as new state *)
    let _, spec_st = state_of_spec_list flds None [spec] in
    let state' = add_neq_constraints state in
    (match check_entailment prog eqs state' spec_st with
      | Ok _ ->
      symb_exec prog flds proc (empty_eqs, spec_st) postcond comms'
      | Error (errs, m) -> mk_error "This split may not hold" errs m pp.pp_pos)
  | Basic (Assume _, _) :: _ -> failwith "TODO Assume SL command"
  | Basic (New _, _) :: _ -> failwith "TODO New command"
  | Basic (Dispose _, _) :: _ -> failwith "TODO Dispose command"
  | Loop _ :: _ -> failwith "TODO Loop command"
  in
  try
    se comms
  with SymbExecFail msg ->
    mk_error msg [] Model.empty pos


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

  match proc.proc_body with
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

        let eqs = empty_eqs in
        symb_exec prog flds proc (eqs, pre) post [comm]
      | Error errs -> errs)
    | Error errs -> errs)
  | None ->
    []

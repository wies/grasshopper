(** {5 Symbolic evaluation of terms and formulas inspired by Viper's Silicon} *)

open Util
open Printf
open Grass
open GrassUtil
open SymbState

(** eval rules *)
let string_of_idset s =
  IdSet.elements s
  |> List.map (fun e -> string_of_ident e)
  |> String.concat ", "
  |> sprintf "[%s]"

(** eval_terms evaluates a term list element-wise using the eval
  functions below, accumulating the resulting symbolic terms into the symb_ts list. *)
let rec eval_terms state (ts: term list) (fc: symb_state -> symb_term list -> 'a option) =
  let rec eeval state tts symb_ts fc =
    match tts with
    | [] -> fc state (List.rev symb_ts) (* reverse due to the cons op below *)
    | hd :: ts' ->
        eval_term state hd (fun state' t ->
          eeval state' ts' (t :: symb_ts) fc)
  in
  eeval state ts [] fc

and eval_term state t (fc: symb_state -> symb_term -> 'a option) =
  Debug.debug(fun() ->
        sprintf "%sEval Term: State:\n{%s\n}\n\n"
        lineSep (string_of_state state));
  match t with
  | Var (id1, srt1) ->
   Debug.debug(fun() ->
        sprintf "%sERIC Var sort (%s)\n" lineSep (string_of_sort srt1));
    (match find_symb_val state.store id1 with
    | Symbt (Var (id2, srt2)) as tt -> 
        if srt1 = srt2
        then fc state tt
        else raise_err (sprintf "sorts are not equal (%s) != (%s), this should never happen!"
          (string_of_sort srt1) (string_of_sort srt2))
    | _ -> raise_err "unreachable found symbval that isn't a Var")
  | App (Value i, [], srt) -> todo "eval Value"
  | App (Union, [], srt) -> todo "eval Union"
  | App (Inter, [], srt) -> todo "eval Inter"
  | App (Read, [map; t], srt) ->
      (match map, t with
      | (App (FreeSym id, [], srt1) | Var (id, srt1)), App (FreeSym x, ts, Loc _)->
          eval_term state t (fun state' t' ->
            let hc = heap_find_by_term state.heap (Symbt (mk_setenum [term_of t'])) in
            let h' = heap_remove state.heap state.pc hc in
            let v = 
              (match maybe_find_symb_val (get_field_store hc) id with
              | Some y -> y 
              | None -> Symbt (mk_free_app srt1 (fresh_ident "v") []))
            in
            let v_map = 
              match v with
              | Symbt (App (FreeSym vfield, _, _)) -> vfield
              | _ -> raise_err "unexpected symb term in eval read"
            in
            let hc_updated = add_to_heap_chunk_map hc id v in
            let h_new, stack = heap_add h' state.pc hc_updated in
            fc {state with heap=h_new; pc=stack} (Symbt (App (FreeSym v_map, ts, srt)))) 
      | _ -> todo "eval read catch all")
  | App (Read, map :: t :: ts, srt) -> todo "eval read"
  | App (Write, [map; t1; t2], srt) -> todo "eval write"

  | App ((Minus | Plus | Mult | Div | Mod | Diff | Inter | Union | Eq | SubsetEq | LtEq | GtEq | Lt | Gt | Elem | AndTerm | OrTerm as sym), [t1; t2], srt) ->
      eval_term state t1 (fun state1 t3 ->
        eval_term state1 t2 (fun state2 t4 ->
          fc state2 (Symbt (App (sym, [term_of t3; term_of t4], srt)))))
  | App (Length, [t], srt) -> todo "eval Length"
  | App (ArrayCells, [t], srt) -> todo "eval ArrayCells"
  | App (SetEnum, ts, srt) ->
    eval_terms state ts (fun state' ts' ->
      fc state' (Symbt (App (SetEnum, List.map (fun t -> term_of t) ts', srt))))
  | App (Destructor d, [t], srt) -> todo "eval Destructor"
  | App (FreeSym id1, ts, srt1) -> 
    Debug.debug (fun () -> sprintf "free sym (%s), srt (%s)\n" (string_of_ident id1) (string_of_sort srt1));
    (match find_symb_val state.store id1 with
    | Symbt (Var (id2, srt2)) as tt -> 
        if srt1 = srt2
        then fc state tt
        else raise_err (sprintf "sorts are not equal (%s) != (%s), this should never happen!"
          (string_of_sort srt1) (string_of_sort srt2))
    | Symbt (App (IntConst n, ts, Int)) as tt ->
        Debug.debug( fun () -> sprintf "IntConst (%s)\n" (string_of_symb_term tt));
        fc state tt
    | _ as tt -> fc state tt)
  | App (IntConst n, [], srt) as i -> 
        Debug.debug (fun () -> sprintf "IntConst (%s)\n" (string_of_term i));
        fc state (Symbt i)
  | App (Null, [], srt) as t-> fc state (Symbt t)
  | App (symb, ts, srt) -> todo "eval App catch all"

(** eval_forms evaluates a formula list fs element-wise using the eval
  function below, accumulating the resulting formulas carrying symbolic values *)
let rec eval_forms state (fs: form list) (fc: symb_state -> symb_form list -> 'a option) =
  let rec eeval state ffs symb_fs fc =
    match ffs with
    | [] -> fc state (List.rev (List.map (fun f -> Symbf f) symb_fs)) (* reverse due to the cons op below *)
    | hd :: ffs' ->
        eval_form state hd (fun state' f ->
          eeval state' ffs' (form_of f :: symb_fs) fc)
  in
  eeval state fs [] fc

and eval_form state f (fc: symb_state -> symb_form -> 'a option) =
  Debug.debug(fun() -> sprintf "eval_form (%s)\n" (Grass.string_of_form f));
  match f with
  | Atom (t, a) -> 
      Debug.debug (fun () -> sprintf "eval_form Atom\n");
      eval_term state t (fun state' t' ->
        Debug.debug (fun () -> sprintf "eval_form done, got term (%s)\n" (string_of_symb_term t'));
        fc state' (Symbf (Atom (term_of t', a))))
  | BoolOp (op, fs) ->
    Debug.debug(fun() -> sprintf "eval_form BoolOp\n");
    eval_forms state fs (fun state' fs' ->
      fc state' (Symbf (BoolOp (op, List.map (fun f -> form_of f) fs'))))
  | Binder (binder, [], f, a) -> 
    Debug.debug(fun() -> sprintf "eval_form Binder, binder(%s)\n" (string_of_form f));
    fc state (Symbf (Binder (binder, [], f, a)))
  | Binder (binder, ts, f, _) -> todo "eval binder catch all"

(** eval_sl_forms evaluates a sl formula list fs element-wise using the eval
  function below, accumulating the resulting formulas carrying symbolic values *)
let rec eval_sl_forms state (fs: Sl.form list) (fc: symb_state -> symb_sl_form list -> 'a option) =
  let rec eeval state ffs symb_fs fc =
    match ffs with
    | [] -> fc state (List.rev symb_fs) (* reverse due to the cons op below *)
    | hd :: ffs' ->
        eval_sl_form state hd (fun state' f ->
          eeval state' ffs' (f :: symb_fs) fc)
  in
  eeval state fs [] fc

and eval_sl_form state f (fc: symb_state -> symb_sl_form -> 'a option) =
  Debug.debug(fun() -> sprintf "eval_form (%s)\n" (Sl.string_of_form f));
  match f with
  | Sl.Pure (ff, pos) ->
      eval_form state ff (fun state' ff' ->
        fc state' (Symbslf (Sl.Pure (form_of ff', pos))))
  | Sl.Atom (symb, ts, pos) -> 
      eval_terms state ts (fun state' ts' ->
        fc state' (Symbslf (Sl.Atom (symb, List.map (fun t -> term_of t) ts', pos))))
  | Sl.SepOp (sop, f1, f2, pos) ->
      eval_sl_form state f1 (fun state2 f3 ->
        eval_sl_form state2 f2 (fun state3 f4 ->
          fc state3 (Symbslf (Sl.SepOp (sop, slform_of f3, slform_of f4, pos)))))
  | Sl.BoolOp (op, slfs, pos) ->
    eval_sl_forms state slfs (fun state' slfs' ->
      fc state' (Symbslf (Sl.BoolOp (op, List.map (fun f -> slform_of f) slfs', pos))))
  | Sl.Binder (b, ids, slf, pos) -> todo "sl binder eval"

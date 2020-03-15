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
let rec eval_terms state (ts: term list) (fc: symb_state -> term list -> 'a option) =
  let rec eeval state tts symb_ts fc =
    match tts with
    | [] -> fc state (List.rev symb_ts) (* reverse due to the cons op below *)
    | hd :: ts' ->
        eval_term state hd (fun state' t ->
          eeval state' ts' (t :: symb_ts) fc)
  in
  eeval state ts [] fc

and eval_term state t (fc: symb_state -> term -> 'a option) =
  Debug.debug (fun () -> sprintf "eval_term with t = (%s)\n" (string_of_term t));
  Debug.debug(fun() ->
        sprintf "%sEval Term: State:\n{%s\n}\n\n"
        lineSep (string_of_state state));
  match t with
  | Var (id1, srt1) ->
    Debug.debug (fun () -> sprintf "var (%s), srt (%s)\n" (string_of_ident id1) (string_of_sort srt1));
    (match find_symb_val state.store id1 with
    | Var (id2, srt2) as tt -> 
        if srt1 = srt2
        then fc state tt
        else raise_err (sprintf "sorts are not equal (%s) != (%s), this should never happen!"
          (string_of_sort srt1) (string_of_sort srt2))
    | _ -> raise_err "unreachable")
  | App (Value i, [], srt) -> todo "eval Value"
  | App (Union, [], srt) -> todo "eval Union"
  | App (Inter, [], srt) -> todo "eval Inter"
  | App (Read, [map; t], srt) ->
      (match map, t with
      | (App (FreeSym id, [], srt1) | Var (id, srt1)), App (FreeSym x, ts, Loc _)->
          eval_term state t (fun state' t' ->
            let hc = heap_find_by_term state.heap (mk_setenum [t']) in
            let h' = heap_remove state.heap state.pc hc in
            let v = 
              (match maybe_find_symb_val (get_field_store hc) id with
              | Some y -> y 
              | None ->
                let vfield = ident_of_symb_val (mk_fresh_symb_val "v" srt) in
                App (FreeSym vfield, [], srt1))
            in
            let v_map = 
              match v with
              | App (FreeSym vfield, _, _) -> vfield
              | _ -> raise_err "unexpected symb term in eval read"
            in
            let hc_updated = add_to_heap_chunk_map hc id v in
            let h_new, stack = heap_add h' state.pc hc_updated in
            fc {state with heap=h_new; pc=stack} (App (FreeSym v_map, ts, srt))) 
      | _ -> todo "eval read catch all")
  | App (Read, map :: t :: ts, srt) -> todo "eval read"
  | App (Write, [map; t1; t2], srt) -> todo "eval write"
  | App ((Minus | Plus | Mult | Div | Mod | Diff | Inter | Union | Eq | SubsetEq | LtEq | GtEq | Lt | Gt | Elem | AndTerm | OrTerm as sym), [t1; t2], srt) ->
      eval_term state t1 (fun state1 t3 ->
        eval_term state1 t2 (fun state2 t4 ->
          fc state2 (App (sym, [t3; t4], srt))))
  | App (Length, [t], srt) -> todo "eval Length"
  | App (ArrayCells, [t], srt) -> todo "eval ArrayCells"
  | App (SetEnum, ts, srt) ->
    eval_terms state ts (fun state' ts' ->
      fc state' (App (SetEnum, ts', srt)))
  | App (Destructor d, [t], srt) -> todo "eval Destructor"
  | App (FreeSym id1, ts, srt1) -> 
    Debug.debug (fun () -> sprintf "free sym (%s), srt (%s)\n" (string_of_ident id1) (string_of_sort srt1));
    (match find_symb_val state.store id1 with
    | Var (id2, srt2) as tt -> 
        if srt1 = srt2
        then fc state tt
        else raise_err (sprintf "sorts are not equal (%s) != (%s), this should never happen!"
          (string_of_sort srt1) (string_of_sort srt2))
    | _ -> raise_err "unreachable")
  | App (IntConst n, [], srt) as i -> 
        Debug.debug (fun () -> sprintf "IntConst (%s)\n" (string_of_term i));
        fc state i 
  | App (Null, [], srt) as t-> fc state t
  | App (symb, ts, srt) -> todo "eval App catch all"


(** eval_forms evaluates a formula list fs element-wise using the eval
  function below, accumulating the resulting formulas carrying symbolic values *)
let rec eval_forms state (fs: form list) (fc: symb_state -> form list -> 'a option) =
  let rec eeval state ffs symb_fs fc =
    match ffs with
    | [] -> fc state (List.rev symb_fs) (* reverse due to the cons op below *)
    | hd :: ffs' ->
        eval_form state hd (fun state' f ->
          eeval state' ffs' (f :: symb_fs) fc)
  in
  eeval state fs [] fc

and eval_form state f (fc: symb_state -> form -> 'a option) =
  Debug.debug(fun() -> sprintf "eval_form (%s)\n" (Grass.string_of_form f));
  match f with
  | Atom (t, a) -> 
      Debug.debug (fun () -> sprintf "eval_form Atom\n");
      eval_term state t (fun state' t' ->
        Debug.debug (fun () -> sprintf "eval_form done, got term (%s)\n" (string_of_term t'));
        fc state' (Atom (t', a)))
  | BoolOp (op, fs) ->
    Debug.debug(fun() -> sprintf "eval_form BoolOp\n");
    eval_forms state fs (fun state' fs' ->
      fc state' (BoolOp (op, fs')))
  | Binder (binder, ts, f, _) -> todo "eval_form Binder"

(** eval_sl_forms evaluates a sl formula list fs element-wise using the eval
  function below, accumulating the resulting formulas carrying symbolic values *)
let rec eval_sl_forms state (fs: Sl.form list) (fc: symb_state -> Sl.form list -> 'a option) =
  let rec eeval state ffs symb_fs fc =
    match ffs with
    | [] -> fc state (List.rev symb_fs) (* reverse due to the cons op below *)
    | hd :: ffs' ->
        eval_sl_form state hd (fun state' f ->
          eeval state' ffs' (f :: symb_fs) fc)
  in
  eeval state fs [] fc

and eval_sl_form state f (fc: symb_state -> Sl.form -> 'a option) =
  Debug.debug(fun() -> sprintf "eval_form (%s)\n" (Sl.string_of_form f));
  match f with
  | Sl.Pure (ff, pos) ->
      eval_form state ff (fun state' ff' ->
        fc state' (Sl.Pure (ff', pos)))
  | Sl.Atom (symb, ts, pos) -> 
      eval_terms state ts (fun state' ts' ->
        fc state' (Sl.Atom (symb, ts', pos)))
  | Sl.SepOp (sop, f1, f2, pos) ->
      eval_sl_form state f1 (fun state2 f3 ->
        eval_sl_form state2 f2 (fun state3 f4 ->
          fc state3 (Sl.SepOp (sop, f3, f4, pos))))
  | Sl.BoolOp (op, slfs, pos) ->
    eval_sl_forms state slfs (fun state' slfs' ->
      fc state' (Sl.BoolOp (op, slfs', pos)))
  | Sl.Binder (b, ids, slf, pos) -> todo "sl binder eval"

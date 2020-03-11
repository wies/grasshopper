(** {5 Symbolic evaluation of terms and formulas inspired by Viper's Silicon} *)

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
  Debug.debug( fun() -> "Inside eval_term \n");
  match t with
  | Var (id1, srt1) ->
    (match find_symb_val state.store id1 with
    | Var (id2, srt2) as tt -> 
        if srt1 = srt2
        then fc state tt
        else raise_err (sprintf "sorts are not equal (%s) != (%s), this should never happen!"
          (string_of_sort srt1) (string_of_sort srt2))
    | _ -> raise_err "unreachable")
  | App (Value i, [], srt) -> todo "eval Value"
  | App (Union, [], _) -> todo "eval Union"
  | App (Inter, [], _) -> todo "eval Inter"
  | App (sym, [], _) when sym <> SetEnum -> todo "eval SetEnum"
  | App (Read, [map; t], _) ->
      (match map, sort_of t with
      | (App (FreeSym _, [], _) | Var _), Loc _ -> todo "eval FreeSym" 
      | _ -> todo "eval read catch all")
  | App (Read, map :: t :: ts, _) -> todo "eval read"
  | App (Write, [map; t1; t2], _) -> todo "eval write"
  | App ((Minus | Plus | Mult | Div | Mod | Diff | Inter | Union | Eq | SubsetEq | LtEq | GtEq | Lt | Gt | Elem | AndTerm | OrTerm as sym), [t1; t2], srt) ->
      eval_term state t1 (fun state1 t3 ->
        eval_term state1 t2 (fun state2 t4 ->
          fc state2 (App (sym, [t3; t4], srt))))
  | App (Length, [t], _) -> todo "eval Length"
  | App (ArrayCells, [t], _) -> todo "eval ArrayCells"
  | App (SetEnum, ts, _) -> todo "eval SetEnum"
  | App (Destructor d, [t], _) -> todo "eval Destructor"
  | App (sym, ts, _) -> todo "eval App catch all"

(** eval_forms evaluates a symbolic formula list fs element-wise using the eval
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
      eval_term state t (fun state' t' ->
        fc state' (Atom (t', a)))
  | BoolOp (op, fs) ->
    Debug.debug(fun() -> sprintf "eval_form BoolOp\n");
    eval_forms state fs (fun state' fs' ->
      fc state' (BoolOp (op, fs')))
  | Binder (binder, ts, f, _) -> todo "eval_form Binder"

(*
let eval_region_term state t (fc: symb_state -> symb_val -> 'a option) =
  match t with
  | App (symb, ts, sort) -> 
      let vv = subst_symbv state t in
      let _ = match vv with
      | Var (id, sort) -> Debug.debug (fun () -> sprintf "REGION TERM EVAL VAR id(%s) srt(%s)\n"
      (string_of_ident id) (string_of_sort sort))
      | App (symbol, ts, sort) -> 
        Debug.debug (fun () -> sprintf "REGION TERM EVAL APP symb(%s) srt(%s)\n"
          (string_of_symbol symbol) (string_of_sort sort))
      in
      let v = subst_symbv state t in
      let _ = match v with
      | Var (id, srt) ->  Debug.debug (fun () -> sprintf "SYMB REGION TERM EVAL VAR id(%s) srt(%s)\n"
      (string_of_ident id) (string_of_sort sort))
      | App (symbol, ts, sort) -> 
        Debug.debug (fun () -> sprintf "Symb REGION TERM EVAL APP symb(%s) srt(%s)\n"
          (string_of_symbol symbol) (string_of_sort sort))
      in
      fc state (Term (subst_symbv state t))
  | _ -> todo "eval region catch all" 

let rec field_read_to_symb_term state  = function
  | App (symb, [App (Grass.Read, [field; var], srt1); t2], srt2) ->
      let field_id = 
        match IdSet.find_first_opt (fun e -> true) (free_consts_term field) with 
         | Some id -> id
         | None -> raise_err "field doesn't have an ident"
      in
      let field_symb = symbol_of field in
      let _ = 
      match field_symb with
      | Some s -> s 
      | None -> raise_err "field doesn't have an ident"
      in
      let field_sort = sort_of field in
      let var_id =
        match IdSet.find_first_opt (fun e -> true) (free_consts_term var) with 
         | Some id -> id
         | None -> raise_err "var doesn't have an ident"
      in
      let var_symb  = 
      match symbol_of var with
      | Some s -> s
      | None -> raise_err "var doesn't have an ident"
      in
      let vv = find_symb_val state.store var_id in
      let var_id = 
        match IdSet.find_first_opt (fun e -> true) (free_consts_term var) with 
         | Some id -> id
         | None -> raise_err "field doesn't have an ident"
      in
      let fv = 
        match heap_find_by_id state.heap (id_of_symb_val vv) with 
        | Obj (_, _, m) ->
         (match IdMap.find_opt field_id m with
          | Some id2 -> id2
          | None -> mk_fresh_symb_val srt1 "r") 
        | Eps _ -> todo()
        | Pred _ -> todo()
      in
      (*TODO add next -> fv to Obj and update heap with Obj(v1, snp, [next -> fv]) *)
      App (symb,
      [
        App (
          Grass.Read, [
            Var (id_of_symb_val fv, srt1);
            Var (id_of_symb_val vv, srt1)
          ], srt1
        ); t2
      ], srt2)
  | App (sym, ts, srt) -> 
      App (sym, List.map (fun el -> (field_read_to_symb_term state) el) ts, srt)
  | t -> t

let field_read_to_fun_form state f = map_terms (field_read_to_symb_term state) f
*)

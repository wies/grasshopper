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

(** eval_ts evaluates a term list element-wise using the eval
  functions below, accumulating the resulting symbolic terms into the symb_ts list. *)
let rec eval_ts state (ts: term list) symb_ts (fc: symb_state -> symb_val list -> 'a option) =
  match ts with
  | [] -> fc state (List.rev symb_ts) (* reverse due to the cons op below *)
  | hd :: ts' -> evalt state hd (fun state' v ->
      Debug.debug(
        fun () ->
          sprintf "eval resolved form into %s\n"
          (string_of_symb_val v)
      );
      eval_ts state' ts' (v :: symb_ts) fc)

and evalt state t (fc: symb_state -> symb_val -> 'a option) =
  (* TODO: Fill this in for commands and other things, not just formulas *)
  Debug.debug(
    fun() ->
      sprintf "eval of term %s\n"
      (string_of_term t)
  );
  eval_term state t fc

and eval_term state t (fc: symb_state -> symb_val -> 'a option) =
  (* should be matching on App any value of type term. *)
  Debug.debug( fun() -> "Inside exec_term \n");
  let v = subst_symbv state t in
  Debug.debug( fun() -> sprintf "Inside exec_term (%s) \n"
    (string_of_term v)
  );
  fc state (Term v)

and evalts state ts (fc: symb_state -> symb_val list -> 'a option) =
  eval_ts state ts [] fc 

and eval_region_term state t (fc: symb_state -> symb_val -> 'a option) =
  match t with
  | Var _ -> todo()
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
(** eval_fs evaluates a symbolic formula list fs element-wise using the eval
  function below, accumulating the resulting symbolic formulas into the fs_symb list. *)
let rec eval_fs state (fs: form list) symb_fs (fc: symb_state -> symb_val list -> 'a option) =
  match fs with
  | [] -> fc state (List.rev symb_fs) (* reverse due to the cons op below *)
  | hd :: fs' -> eval state hd (fun state' v ->
      eval_fs state' fs' (v :: symb_fs) fc)

and eval_form state f (fc: symb_state -> symb_val -> 'a option) =
  Debug.debug(fun() -> sprintf "eval_form (%s)\n" (Grass.string_of_form f));
  match f with
  | Atom (Var (id, srt), _) ->
    Debug.debug(fun() -> sprintf "eval_form Atom Var (%s)\n" (Grass.string_of_form f));
    let subs = subst_symbv state in
    fc state (Form (map_terms subs f))

  | Atom (App (symb, [App (Grass.Read, [var_id; field_id], srt1); t2], srt2), _) ->
    Debug.debug(fun() -> sprintf "eval_form Atom App 2x (%s) \n" (Grass.string_of_form f));
    fc state (Form (field_read_to_fun_form state f))

  | Atom (App (symb, [t], srt), _) ->
    Debug.debug(fun() -> sprintf "eval_form Atom App 1x (%s) \n" (Grass.string_of_form f));
    let subs = subst_symbv state in
    fc state (Form (map_terms subs f))
  | Atom (App (symb, ts, srt), _) ->
    Debug.debug(fun() -> sprintf "eval_form Atom App all (%s) \n" (Grass.string_of_form f));
    let subs = subst_symbv state in
    fc state (Form (map_terms subs f))
  | BoolOp (op, fs) ->
    Debug.debug(fun() -> sprintf "eval_form op(e_bar) (%s)\n" (Grass.string_of_form f));
    let subs = subst_symbv state in
    fc state (Form (map_terms subs f))
  | Binder (binder, ts, f, _) -> 
    Debug.debug(fun() -> sprintf "eval_form binder (%s)\n" (Grass.string_of_form f));
    let subs = subst_symbv state in
    fc state (Form (map_terms subs f))
and eval state f (fc: symb_state -> symb_val -> 'a option) =
  (* TODO: Fill this in for commands and other things, not just formulas *)
  eval_form state f fc

and eval_binder state binding ts f1 (fc: symb_state -> symb_val -> 'a option) = todo()

(** evals evaulates a list of formulas by calling evals_substituted which
 processes the provided formulas one-by-one passing the evaluated formula
 to it's continuation, which builds a list of formulas with symbolic values
 substituted *)
and evals state fs (fc: symb_state -> symb_val list -> 'a option) = 
  eval_fs state fs [] fc

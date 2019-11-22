(** {5 Symbolic evaluation of terms and formulas inspired by Viper's Silicon} *)

open Printf
open Grass
open SymbState

(** eval rules *)

(** evals_subs evaluates a symbolic formula list element-wise using the exec
  function below, accumulating the resulting symbolic formulas into the fs_symb list. *)
let rec evals_subs state fs symb_fs (fc: symb_state -> symb_val list -> 'a option) =
  match fs with
  | [] -> fc state (List.rev symb_fs) (* reverse due to the cons op below *)
  | hd :: fs' -> eval state hd (fun state' v ->
      evals_subs state' fs' (v :: symb_fs) fc)

and eval state f (fc: symb_state -> symb_val -> 'a option) =
  match f with
  | Grass.Atom (t, _) -> eval_term state t fc
  | Grass.BoolOp (op, fs) -> eval_forms state fs fc
  | Grass.Binder (b, ts, f1, _) -> eval_binder state b ts f1 fc
  
and eval_term state t (fc: symb_state -> symb_val -> 'a option) =
  let symbv =
    match t with
    | Var (id, _) -> 
      IdMap.find_opt id state.store 
    | App (_, _, _) -> None
  in
  match symbv with
  | Some v -> fc state v
  | None -> Some ("term: " ^ (string_of_term t) ^ " not found in store")

and eval_forms state fs (fc: symb_state -> symb_val -> 'a option) =
  match fs with
  | [] -> todo()
  | [f] ->  todo()
  | f :: fs' ->
      match f with
      | Atom (t, _) ->
        (match t with
        | Var (id, srt) ->
          let symbv = find_symb_val state.store id in
          Debug.debug(
            fun () -> sprintf "%sEval Forms Atom Var (%s, %s) has symb val %s\n" 
            lineSep (string_of_ident id) (string_of_sort srt) (string_of_symb_val symbv)
          );
          todo()
        | App (sym, ts, srt) ->
          Prog.pr_term_list Format.std_formatter ts;
          Debug.debug(
            fun () -> sprintf "%sEval Forms Atom App (%s, %s)\n" 
            lineSep (string_of_symbol sym) (string_of_sort srt)
          )); todo();
          
      | BoolOp (op, fs)  -> 
          Debug.debug(
            fun () -> sprintf "%sEval BoolOp OR\n" 
            lineSep
          ); todo()
      | Binder (b, ts, f1, _) -> 
          Debug.debug(
            fun () -> sprintf "%sEval BoolOp OR\n" 
            lineSep
          ); todo()

and eval_binder state binding ts f1 (fc: symb_state -> symb_val -> 'a option) = todo()

(** evals evaulates a list of formulas by calling evals_substituted which
 processes the provided formulas one-by-one passing the evaluated formula
 to it's continuation, which builds a list of formulas with symbolic values
 substituted *)
and evals state fs (fc: symb_state -> symb_val list -> 'a option) = 
  evals_subs state fs [] fc

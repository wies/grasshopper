(** {5 Symbolic evaluation of terms and formulas inspired by Viper's Silicon} *)

open Grass
open SymbState

let eval_term state t (fc: symb_state -> symb_val -> 'a option) =
  let symbv =
    match t with
    | Var (id, _) -> 
      IdMap.find_opt id state.store 
    | App (_, _, _) -> None
  in
  match symbv with
  | Some v -> fc state v
  | None -> Some ("term: " ^ (string_of_term t) ^ " not found in store")

let eval_boolop state op fs (fc: symb_state -> symb_val -> 'a option) =
  match fs with
  | [] -> None
  | hd :: fs' -> todo()

let eval_binder state binding ts f1 (fc: symb_state -> symb_val -> 'a option) = todo()

(** eval evaluates an expression *)
let eval_form state f fc = 
  match f with
  | Atom (t, _) -> eval_term state t fc      
  | BoolOp (op, fs) -> eval_boolop state op fs fc
  | Binder (b, ts, f1, _) -> eval_binder state b ts f1 fc

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

(** eval_fs evaluates a symbolic formula list fs element-wise using the eval
  function below, accumulating the resulting symbolic formulas into the fs_symb list. *)
let rec eval_fs state (fs: form list) symb_fs (fc: symb_state -> symb_val list -> 'a option) =
  match fs with
  | [] -> fc state (List.rev symb_fs) (* reverse due to the cons op below *)
  | hd :: fs' -> eval state hd (fun state' v ->
      Debug.debug(
        fun () ->
          sprintf "eval resolved form into %s\n"
          (string_of_symb_val v)
      );
      eval_fs state' fs' (v :: symb_fs) fc)

and eval state f (fc: symb_state -> symb_val -> 'a option) =
  (* TODO: Fill this in for commands and other things, not just formulas *)
  Debug.debug(
    fun() ->
      sprintf "eval of formula %s\n"
      (string_of_form f)
  );
  eval_form state f fc

and eval_form state f (fc: symb_state -> symb_val -> 'a option) =
  let rec subst_symbv = function
    | App (symb, ts, srt) as a -> 
      let ids = free_consts_term a in
      let idslst = IdSet.elements ids in
      let sm = 
        idslst |> List.fold_left (fun sm e ->
          (match find_symb_val state.store e with
          | Term (Var (id2, srtt)) ->
            Debug.debug(
              fun () ->
                sprintf "found symb v %s\n"
                (string_of_ident id2)
            );
            IdMap.add e id2 sm 
          | Term (App (_, _, _)) -> failwith "shouldn't get an App as a symb val"
          | Form _ -> failwith "shouldn't get a form in a symb val")
        ) IdMap.empty
      in
      let subv = subst_id_term sm a in
      Debug.debug(
        fun () ->
          sprintf " substutituted val is %s\n"
          (string_of_term subv)
      );
      subv
    | Var (id, srt) ->
      let v = find_symb_val state.store id in
      (match v with
      | Term (Var (id2, srtt)) -> Var (id2, srt)
      | Term (App (_, _, _)) -> failwith "shouldn't get an App as a symb val"
      | Form _ -> failwith "shouldn't get a form in a symb val")
  in
  fc state (Form (map_terms subst_symbv f))

and eval_binder state binding ts f1 (fc: symb_state -> symb_val -> 'a option) = todo()

(** evals evaulates a list of formulas by calling evals_substituted which
 processes the provided formulas one-by-one passing the evaluated formula
 to it's continuation, which builds a list of formulas with symbolic values
 substituted *)
and evals state fs (fc: symb_state -> symb_val list -> 'a option) = 
  eval_fs state fs [] fc



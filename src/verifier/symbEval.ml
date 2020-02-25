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

(** subst_symbv takes a formula and substitutes all terms with corresponding
 * symbolic variables in the symbolic store carried in state *)
let rec subst_symbv state = function
  | App (symb, _, srt) as a -> 
    Debug.debug (fun () -> sprintf "subst_symbv App (%s)\n"
    (string_of_symbol symb));
    let ids = free_consts_term a in
    IdSet.map (fun id -> 
      Debug.debug (fun () -> sprintf "ids App (%s)\n"
        (string_of_ident id));
        id
    ) ids;
    let idslst = IdSet.elements ids in
    let sm = 
      idslst |> List.fold_left (fun sm e ->
        (match find_symb_val state.store e with
        | Term (Var (id2, srtt)) ->
          IdMap.add e id2 sm 
        | Term (App (IntConst ic, [], _)) ->
            Debug.debug( fun () -> sprintf "App IntConst \n");
            sm
        | Term (App (_, _, _)) -> sm 
        | Form _ -> sm
      )) IdMap.empty
    in
    let subv = subst_id_term sm a in
    subv
  | Var (id, srt) ->
    Debug.debug(fun () -> sprintf "subst_symbv (%s)\n"
    (string_of_ident id));
    let v = find_symb_val state.store id in
    (match v with
    | Term (Var (id2, srtt)) -> Var (id2, srt)
    | Term (App (_, _, _)) -> failwith "shouldn't get an App as a symb val"
    | Form _ -> failwith "shouldn't get a form in a symb val")

(** eval_fs evaluates a symbolic formula list fs element-wise using the eval
  function below, accumulating the resulting symbolic formulas into the fs_symb list. *)
let rec eval_fs state (fs: form list) symb_fs (fc: symb_state -> symb_val list -> 'a option) =
  match fs with
  | [] -> fc state (List.rev symb_fs) (* reverse due to the cons op below *)
  | hd :: fs' -> eval state hd (fun state' v ->
      eval_fs state' fs' (v :: symb_fs) fc)

and eval state f (fc: symb_state -> symb_val -> 'a option) =
  (* TODO: Fill this in for commands and other things, not just formulas *)
  eval_form state f fc

and eval_form state f (fc: symb_state -> symb_val -> 'a option) =
  Debug.debug(fun() -> sprintf "eval_form (%s)\n" (Grass.string_of_form f));
  let subs = subst_symbv state in
  fc state (Form (map_terms subs f))

and eval_binder state binding ts f1 (fc: symb_state -> symb_val -> 'a option) = todo()

(** evals evaulates a list of formulas by calling evals_substituted which
 processes the provided formulas one-by-one passing the evaluated formula
 to it's continuation, which builds a list of formulas with symbolic values
 substituted *)
and evals state fs (fc: symb_state -> symb_val list -> 'a option) = 
  eval_fs state fs [] fc

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
      sprintf "eval of formula %s\n"
      (string_of_term t)
  );
  eval_term state t fc

and eval_term state t (fc: symb_state -> symb_val -> 'a option) =
  Debug.debug( fun() -> "Inside exec_term \n");
  let v = subst_symbv state t in
  Debug.debug( fun() -> sprintf "Inside exec_term (%s) \n"
    (string_of_term v)
  );
  fc state (Term v)

and evalts state ts (fc: symb_state -> symb_val list -> 'a option) =
  eval_ts state ts [] fc 

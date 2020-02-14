(** {5 Symbolic execution inspired by Viper's Silicon} *)

open Printf
open GrassUtil
open Grass
open SymbState 

exception SymbExecFail of string
let raise_err str = raise (SymbExecFail str)

(** Helpers to format prints *)
let lineSep = "\n--------------------\n"

let string_of_symb_val v =
    match v with
    | Term t -> string_of_term t
    | Form f -> string_of_form f

let string_of_pcset s =
  s
  |> List.map (fun ele -> (string_of_symb_val ele))
  |> String.concat ", "

let string_of_symb_val_list vals =
  vals
  |> List.map (fun v -> (string_of_symb_val v))
  |> String.concat ", "
  |> sprintf "[%s]"

let string_of_symb_store s =
  IdMap.bindings s
  |> List.map (fun (k, v) -> (string_of_ident k) ^ ":" ^ (string_of_symb_val v))
  |> String.concat ", "
  |> sprintf "{%s}"

let string_of_symb_val_map store =
  IdMap.bindings store
  |> List.map (fun (k, v) -> (string_of_ident k) ^ ":" ^ (string_of_symb_val v))
  |> String.concat ", "
  |> sprintf "{%s}"

let string_of_symb_fields fields =
  IdMap.bindings fields
  |> List.map (fun (k, v) -> (string_of_ident k) ^ ":" ^ (string_of_symb_val v))
  |> String.concat ", "
  |> sprintf "{%s}"

let string_of_pc_stack pc =
  pc
  |> List.map (fun (pc, bc, vars) ->
      "(" ^ (string_of_ident pc) ^ ", " ^ (string_of_symb_val bc) ^ ", "
      ^ (string_of_pcset vars) ^ ")")
  |> String.concat ", "
  |> sprintf "[%s]"

let rec string_of_snap s =
  match s with
  | Unit -> "unit[snap]"
  | Snap ss -> string_of_symb_val ss
  | SnapPair (s1, s2) ->
      sprintf "%s(%s)" (string_of_snap s1) (string_of_snap s2)

let string_of_hc chunk =
  match chunk with
  | Obj (v, snap, symb_fields) ->
    sprintf "Obj(%s, Snap:%s, Fields:%s)" (string_of_symb_val v)
      (string_of_snap snap) (string_of_symb_fields symb_fields)
  | Pred (id, symb_vals) -> sprintf "Pred(Id:%s, Args:%s)" (string_of_ident id)
      (string_of_symb_val_list symb_vals)

let string_of_heap h =
  h
  |> List.map (fun ele -> (string_of_hc ele))
  |> String.concat ", "
  |> sprintf "[%s]"

let string_of_state s =
  let store = string_of_symb_store s.store in
  let old_store = string_of_symb_store s.old_store in
  let pc = string_of_pc_stack s.pc in
  let heap = string_of_heap s.heap in
  sprintf "\n\tStore: %s,\n\tOld Store: %s\n\tPCStack: %s\n\tHeap: %s" store old_store pc heap

 (*
let assert_constr pc_stack v =
  (** TODO add pred_axioms to pc_stack before passing in *)
  if check pc_stack v then None else None
  *) 

(* Returns None if the entailment holds, otherwise Some (list of error messages, model) *)
(** carry over from Sid's SymbExec *)
let check_entail prog p1 p2 =
  if p1 = p2 || p2 = mk_true then None
  else (* Dump it to an SMT solver *)
    (** TODO: collect program axioms and add to symbolic state *)
    let p2 = Verifier.annotate_aux_msg "Related location" p2 in
    (* Close the formulas: assuming all free variables are existential *)
    let close f = smk_exists (Grass.IdSrtSet.elements (sorted_free_vars f)) f in
    let labels, f =
      smk_and [p1; mk_not p2] |> close |> nnf
      (* Add definitions of all referenced predicates and functions *)
      |> fun f -> f :: Verifier.pred_axioms prog
      (** TODO: Add axioms *)
      |> (fun fs -> smk_and fs)
      (* Add labels *)
      |> Verifier.add_labels
    in
    let name = fresh_ident "form" |> Grass.string_of_ident in
    Debug.debug (fun () ->
      sprintf "\n\nCalling prover with name %s\n" name);
    match Prover.get_model ~session_name:name f with
    | None -> None
    | Some model -> Some (Verifier.get_err_msg_from_labels model labels, model)

(** SMT solver calls *)
let check pc_stack prog v =
  let constr = pc_collect_constr pc_stack in
  let forms = List.map
    (fun v ->
      match v with
      | Term t ->
          Debug.debug(fun () -> sprintf "check term %s\n"
          (string_of_term t)
          );
          Atom (t, [])
      | Form f -> 
          Debug.debug(fun () -> sprintf "check form %s\n"
          (string_of_form f));
          f)
    constr
  in
  match check_entail prog (smk_and forms) v  with 
  | Some errs -> raise_err "SMT check failed"
  | None -> ()

let symb_val_to_form v = 
  match v with
  | Term t -> todo() 
  | Form f -> f

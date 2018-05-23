(** {5 Model read-eval-print-loop} *)

open Util
open Grass
open GrassUtil
open SplSyntax
open Model
open Printf


exception Unsupported of string
let fail str = raise (Unsupported str)


let rec term_of_expr model e =
  let get_sign sym = match SymbolMap.find_opt sym model.sign with
    | Some [arity] -> arity
    | None | Some [] ->
      fail (sprintf "Couldn't find %s in signature" (string_of_symbol sym))
    | Some arities -> 
      fail (sprintf "Symbol %s has multiple arities: %s"
        (string_of_symbol sym)
        (arities |> List.map string_of_arity |> String.concat ", "))
  in

  match e with
  | IntVal (i, _) -> mk_int64 i
  | BoolVal (b, _) -> mk_bool_term b
  | Ident (id, _) ->
    let sym = FreeSym id in
    (match get_sign sym with
    | ([], srt) -> mk_const srt sym
    | arity ->
      fail (sprintf "Got Ident %s with non-const sort %s" (string_of_ident id) 
              (string_of_arity arity)))
  | Read (Ident (id, _), t, _) when SymbolMap.mem (Destructor id) model.sign ->
    let t = term_of_expr model t in
    (match get_sign (Destructor id) with
    | ([_], res_s) ->
      App (Destructor id, [t], res_s)
    | arity ->
      fail (sprintf "Symbol %s has arity %s but was applied to %s: %s"
        (string_of_ident id) (string_of_arity arity)
        (string_of_term t) (sort_of t |> string_of_sort)))
  | Read ((Ident (("length", _), _)), idx, _) ->
    mk_length (term_of_expr model idx)
  | Read (map, t, _) ->
    let map = term_of_expr model map in
    let t = term_of_expr model t in
    mk_read map [t]
  | ProcCall (id, ts, _)
  | PredApp (Pred id, ts, _) -> (* Function application *)
    let ts = List.map (term_of_expr model ) ts in
    let sym = FreeSym id in
    let (arg_srts, res_srt) = get_sign sym in
    mk_app res_srt sym ts
  | BinaryOp (e1, op, e2, _, _) as e ->
    let mk_t = match op with
      | OpDiff -> mk_diff
      | OpInt -> fun t1 t2 -> mk_inter [t1; t2]
      | OpMinus -> mk_minus
      | OpPlus -> mk_plus
      | OpMult -> mk_mult
      | OpDiv -> mk_div
      | OpMod -> mk_mod
      | OpEq -> mk_eq_term
      | OpGt -> mk_gt_term
      | OpLt -> mk_lt_term
      | OpGeq -> mk_geq_term
      | OpLeq -> mk_leq_term
      | OpIn -> mk_elem_term
      | OpBvAnd -> GrassUtil.mk_bv_and
      | OpBvOr -> GrassUtil.mk_bv_or
      | OpBvShiftL -> GrassUtil.mk_bv_shift_left
      | OpBvShiftR -> GrassUtil.mk_bv_shift_right
      | _ -> fail ("TODO: can't yet handle: " ^ string_of_expr e)
    in
    mk_t (term_of_expr model e1) (term_of_expr model e2)
  | e -> fail ("TODO: can't yet handle: " ^ string_of_expr e)

let repl model =
  printf "\nModel:\nintp:\n";
  SortedSymbolMap.iter (fun (sym, ar) (m, d) ->
    printf "  %s: %s = {%s} | def: ??\n" (string_of_symbol sym) (string_of_arity ar)
      (ValueListMap.bindings m
      |> List.map (fun (vs, v) ->
        (List.map string_of_value vs |> String.concat ", ") ^ " : " ^ (string_of_value v))
      |> String.concat ", ")
    ) model.intp;
  (* printf "vals:\n";
  SortedValueMap.iter (fun (v, s) ev ->
    printf "  %s: %s = ??\n" (string_of_value v) (string_of_sort s)) model.vals; *)

  print_endline "\nModel REPL. Press Ctrl-D to quit.";
  let rec repl_loop () =
    try
      print_string " > " ; flush stdout;
      let lexbuf = Lexing.from_string (read_line ()) in
      let e = SplParser.expr SplLexer.token lexbuf in
      let t = term_of_expr model e in
      let v = Model.eval model t in
      print_endline @@ string_of_eval model (sort_of t) v;
      repl_loop ()
    with
    | Parsing.Parse_error ->
      print_string "Syntax error.\n";
      Parsing.clear_parser ();
      repl_loop ()
    | Unsupported str
    | Failure str ->
      print_string @@ "Error: " ^ str ^ "\n";
      Parsing.clear_parser ();
      repl_loop ()
    | Undefined ->
      print_string "Error: Model says undefined.\n";
      Parsing.clear_parser ();
      repl_loop ()
    | Not_found ->
      print_string "Error: Model says Not_found.\n";
      Parsing.clear_parser ();
      repl_loop ()
    | End_of_file -> print_endline "\n";
  in
  repl_loop ()

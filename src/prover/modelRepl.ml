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
  | Read (map, t, _) ->
    let map = term_of_expr model map in
    let t = term_of_expr model t in
    mk_read map [t]
  | ProcCall (id, ts, _)
  | PredApp (Pred id, ts, _) ->
    let ts = List.map (term_of_expr model ) ts in
    let sym = FreeSym id in
    let (arg_srts, res_srt) = get_sign sym in
    mk_app res_srt sym ts
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
      print_string "Model: Undefined.\n";
      Parsing.clear_parser ();
      repl_loop ()
    | End_of_file -> print_endline "\n";
  in
  repl_loop ()

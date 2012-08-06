open Form
open Stmnt
open Axioms
open Util
open Logging

let input_file = ref ""

type mode =
  | Interpolate
  | SlSat
  | SlEntails

let mode = ref Interpolate

let cmd_options =
  [("-v", Arg.Set Debug.verbose, "Display verbose messages");
   ("-noreach", Arg.Clear Axioms.with_reach_axioms, "Do not add axioms for reachability predicates");
   ("-m", Arg.Set_string Prover.model_file, "Produce model");
   ("-alloc", Arg.Set Axioms.with_alloc_axioms, "Add axioms for alloc predicate");
   ("-nojoin", Arg.Clear Axioms.with_jp_axioms, "Do not add axioms for join functions");
   ("-sl", Arg.Unit (fun () -> mode := SlSat), "SL satisfiability");
   ("-sl2", Arg.Unit (fun () -> mode := SlEntails), "SL satisfiability")
  ]

let usage_message =
  "Usage:\n  " ^ Sys.argv.(0) ^ 
  " [-v] [-noreach] [-nojoin] <input file>\n"

let cmd_line_error msg =
  Arg.usage cmd_options usage_message;
  failwith ("Command line option error: " ^ msg)

let parse_input parse_fct =
  let input = read_file !input_file in
  ParseStmntAux.input := Some input;
  let lexbuf = Lexing.from_string input in
  ParseStmntAux.buffer := Some lexbuf;
  parse_fct lexbuf

let compute_interpolant () =
  let path = parse_input (fun lexbuf -> ParseStmnt.main LexStmnt.token lexbuf) in
  let pf_a, pf_b = path_form path in
  (* let _ = if !Debug.verbose then print_forms stdout [mk_and pf_a; mk_and pf_b] in *)
  let interpolant = Prover.interpolate pf_a pf_b in
  let _ = Printf.fprintf stdout "accumulated time: %.2fs\n" !Util.measured_time in
  print_form stdout interpolant

let compute_sl_sat () =
  (*print_endline "parsing";*)
  let sl = parse_input (fun lexbuf -> ParseSl.main LexSl.token lexbuf) in
  let _ = Debug.msg ("parsed: " ^ (Sl.to_string sl) ^ "\n") in
  let sln = Sl.normalize sl in
  let _ = Debug.msg ("normalized: " ^ (Sl.to_string sln) ^ "\n") in
  let form = Sl.to_form sln in
  let _ = if !Debug.verbose then
    begin
      print_endline "converted: ";
      print_form stdout form
    end
  in
  (*print_endline "to prover";*)
  let res = Prover.satisfiable form in
    Printf.fprintf stdout "accumulated time: %.2fs\n" !Util.measured_time;
    match res with
    | Some true -> print_endline "sat"
    | Some false -> print_endline "unsat"
    | None -> print_endline "unknown"

let compute_sl_entails () =
  let pre_heap = mk_ident "A" in
  let post_heap = mk_ident "B" in
  (* check that sp(pre, path) |- post *)
  let (pre_sl, path, post_sl) = parse_input (fun lexbuf -> ParseSl2.main LexSl2.token lexbuf) in
  let path_wo_label = List.filter (function Label _ -> false | _ -> true) path in
  (* convert wo axioms and add axioms later *)
  let pre_sl_n = Sl.normalize pre_sl in
  let pre = Sl.to_form_without_axioms pre_sl_n in
  let tight_pre = Sl.tightness pre_heap pre_sl_n in
  let post_sl_n = Sl.normalize post_sl in
  let post = Sl.to_form_without_axioms post_sl_n in
  let tight_post = Sl.tightness post_heap post_sl_n in
  (* ssa *)
  let (pref, pre_sl_axioms, pathf, postf, post_sl_axioms) =
    match ssa_form ((Assume pre) ::
                    (Label "dummy") ::
                    (Assume tight_pre) ::
                    (Label "dummy") ::
                    path_wo_label @
                    [(Label "dummy");
                     (Assume post);
                     (Label "dummy");
                     (Assume tight_post)])
    with
    | [a; b; c; d; e] -> (a, b, c, d, e)
    | _ -> failwith "ssa_form did not return the expected number of formula"
  in
  let _ = if !Debug.verbose then
    begin
      print_endline "parsed: ";
      print_endline ("pre: " ^ (Sl.to_string pre_sl));
      print_endline "pre axioms:";
      List.iter (print_form stdout) pre_sl_axioms;
      print_endline "pre converted:";
      List.iter (print_form stdout) pref;

      print_endline "path: ";
      List.iter (print_form stdout) pathf;

      print_endline ("post: " ^ (Sl.to_string post_sl));
      print_endline "post axioms:";
      List.iter (print_form stdout) post_sl_axioms;
      print_endline "post converted:";
      List.iter (print_form stdout) postf
    end
  in
  (* need to skolemize the post_sl_axioms *)
  let fresh () = mk_const (fresh_ident "sk_var") in
  let post_skolem = List.map (skolemize fresh) post_sl_axioms in
  (* axioms from the logic *)
  let (prea, patha, posta) = match add_axioms [ pref; pathf; postf] with
    | [a; b; c] -> (a,b,c)
    | _ -> failwith "ssa_form did not return the expected number of formula"
  in
  (* add forall x. A(x) <=> B(x) *)
  let a_x = mk_pred pre_heap [var1] in
  let b_x = mk_pred post_heap [var1] in
  let same_heap_content = mk_or [mk_and [a_x; b_x]; mk_and [mk_not a_x; mk_not b_x]] in
  (* query *)
  let query = smk_and ( same_heap_content ::
                        pref @ pre_sl_axioms @ prea @
                        pathf @ patha @
                        [nnf (mk_not (smk_and (postf @ post_skolem)))] @ posta )
  in
  let _ = if !Debug.verbose then
    begin
      print_endline "query: ";
      print_form stdout query
    end
  in
  let res = Prover.satisfiable query in
    Printf.fprintf stdout "accumulated time: %.2fs\n" !Util.measured_time;
    match res with
    | Some true -> print_endline "not entailed"
    | Some false -> print_endline "entailed"
    | None -> print_endline "unknown"

let _ =
  try
    Arg.parse cmd_options (fun s -> input_file := s) usage_message;
    if !input_file = "" then cmd_line_error "input file missing" else
      begin
        match !mode with
        | Interpolate -> compute_interpolant ()
        | SlSat -> compute_sl_sat ()
        | SlEntails -> compute_sl_entails ()
      end
  with  
  | Sys_error s -> output_string stderr (s ^ "\n")
  | Failure s -> output_string stderr (s ^ "\n")
  | Parsing.Parse_error -> print_endline "parse error"
	
    

(** Auxiliary file used to avoid module recursion,
   stores error handling routing for the generated {!Stmnt.path} parser. *)

open Lexing

type bufp = Lexing.lexbuf option ref 

let (input : string option ref) = ref None
let (buffer : bufp) = ref None

let marker = " <*> "

let parse_error s = match !input with
| Some inp -> (match !buffer with
  | Some buf ->
      let pos = buf.lex_curr_p.pos_cnum in
      let init = String.sub inp 0 pos in
      let rest = String.sub inp pos (String.length inp - pos) in
      output_string stderr ("Parse error:\n" ^ init ^ marker ^ rest ^ "\n")
  | _ -> output_string stderr ("Parse error in uninitialized parse state1.\n"))
| _ -> output_string stderr ("Parse error in uninitialized parse state.\n")

let parse_buf_exn rule lexer lexbuf =
  try
    rule lexer lexbuf
  with exn ->
    begin
      parse_error "";
      exit 1
    end

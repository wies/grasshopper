open Prog

exception Prog_error of source_position * string

let lexical_error pos = raise (Prog_error (pos, "Lexical Error"))

let syntax_error pos = raise (Prog_error (pos, "Syntax Error"))

let type_error pos msg = raise (Prog_error (pos, "Type Error: " ^ msg))

let error pos msg = raise (Prog_error (pos, "Error: " ^ msg))

let to_string = function
  | Prog_error (pos, msg) -> Printf.sprintf "%s:\n%s" (string_of_src_pos pos) msg
  | e -> raise (Invalid_argument "ProgError.to_string: expected a program error exception")

let print_error pos msg = print_endline (to_string (Prog_error (pos, msg)))

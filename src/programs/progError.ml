open Programs

exception Prog_error of source_position * string

let lexical_error pos = raise (Prog_error (pos, "Lexical Error"))

let syntax_error pos = raise (Prog_error (pos, "Syntax Error"))

let type_error pos msg = raise (Prog_error (pos, "Type Error: " ^ msg))

let error pos msg = raise (Prog_error (pos, "Error: " ^ msg))

let to_string = function
  | Prog_error (pos, msg) ->
      if pos.sp_end_line = pos.sp_start_line 
      then Printf.sprintf "File \"%s\", line %d, characters %d-%d:\n%s" 
          pos.sp_file pos.sp_start_line pos.sp_start_col pos.sp_end_col msg
      else Printf.sprintf "File \"%s\", line %d, character %d - line %d, character %d:\n%s" 
          pos.sp_file pos.sp_start_line pos.sp_start_col pos.sp_end_line pos.sp_end_col msg
  | e -> raise (Invalid_argument "ProgError.to_string: expected a program error exception")

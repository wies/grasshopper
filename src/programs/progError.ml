open Grass

exception Prog_error of source_position * string

let flycheck_string_of_src_pos pos =
  if pos.sp_start_line <> pos.sp_end_line 
  then Printf.sprintf "%s:%d:%d" pos.sp_file pos.sp_start_line pos.sp_start_col
  else 
    let start_col, end_col = 
      if pos.sp_start_col = pos.sp_end_col 
      then 
        if pos.sp_start_col = 0 
        then 0, 1
        else pos.sp_start_col - 1, pos.sp_end_col
      else pos.sp_start_col, pos.sp_end_col
    in
    Printf.sprintf "%s:%d:%d-%d" pos.sp_file pos.sp_start_line start_col end_col

let lexical_error pos = raise (Prog_error (pos, "Lexical Error"))

let syntax_error pos msg_opt = 
  match msg_opt with 
  | Some msg -> raise (Prog_error (pos, "Syntax Error: " ^ msg))
  | None -> raise (Prog_error (pos, "Syntax Error"))

let type_error pos msg = raise (Prog_error (pos, "Type Error: " ^ msg))

let error pos msg = raise (Prog_error (pos, "Error: " ^ msg))

let error_to_string pos msg = 
  if pos = GrassUtil.dummy_position 
  then msg 
  else
    if !Config.flycheck_mode 
    then Printf.sprintf "%s:%s" (flycheck_string_of_src_pos pos) msg
    else Printf.sprintf "%s:\n%s" (string_of_src_pos pos) msg

let to_string = function
  | Prog_error (pos, msg) -> error_to_string pos msg      
  | e -> raise (Invalid_argument "ProgError.to_string: expected a program error exception")

let print_error pos msg = print_endline (to_string (Prog_error (pos, msg)))

let mk_trace_info msg = "Trace Information: " ^ msg

let mk_error_info msg = "Related Location: " ^ msg

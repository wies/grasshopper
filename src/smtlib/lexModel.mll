{
open Form
open FormUtil
open ParseModel

let symbol_tbl = Hashtbl.create 7
let sort_tbl = Hashtbl.create 7

let _ = List.iter (fun sym -> Hashtbl.add symbol_tbl (str_of_symbol sym, 0) sym) symbols

let _ = List.iter (fun (id, srt) -> Hashtbl.add sort_tbl id srt) 
    [bool_sort_string, Bool;
     loc_sort_string, Loc;
     loc_sort_string, Int;
     fld_sort_string, Fld Loc;
     set_sort_string, Set Loc]

let to_symbol id =
  try Hashtbl.find symbol_tbl id 
  with Not_found -> FreeSym id

let to_sort id = Hashtbl.find sort_tbl id 

}

let digitchar = ['0'-'9']
let identchar = ['a'-'z' 'A'-'Z' '_' '!' '?' '$']
let ident = identchar (identchar | digitchar)*

rule token = parse
  [' ' '\t' '\n'] { token lexbuf }
| '{' { LBRACE }
| '}' { RBRACE }
| "->" { ARROW }
| "else" { ELSE }
| "true" { VAL(Bool, BoolConst true) }
| "false" { VAL(Bool, BoolConst false) }
| "#unspecified" { UNSPEC }
| (ident as srt) "!val!" (digitchar+ as num) { VAL(to_sort srt, FreeSym (srt ^ "!" ^ num,0)) }
| ident as name '_' (digitchar+ as num) { SYMBOL(to_symbol (name, int_of_string num)) }
| ident as name '_' (digitchar+ as num) "!" digitchar+ { SYMBOL(to_symbol (name, int_of_string num)) }
| ident as name "!" digitchar+ { SYMBOL(to_symbol (name, 0)) }
| ident as name { SYMBOL(to_symbol (name, 0)) }
| eof { EOF }

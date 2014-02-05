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
     int_sort_string, Int;
     fld_sort_string^loc_sort_string, Fld Loc;
     fld_sort_string^int_sort_string, Fld Int;
     fld_sort_string^bool_sort_string, Fld Bool;
     set_sort_string^loc_sort_string, Set Loc;
     set_sort_string^int_sort_string, Set Int
    ]

let to_symbol id =
  try Hashtbl.find symbol_tbl id 
  with Not_found -> FreeSym id

let to_sort id = Hashtbl.find sort_tbl id 

}

let digitchar = ['0'-'9']
let identchar = ['a'-'z' 'A'-'Z' '?']
let identchar2 = '_'? identchar
let ident = identchar2 (identchar2 | digitchar)*

let permissive_identchar = ['a'-'z' 'A'-'Z' '_' '!' '?' '$']
let permissive_ident = permissive_identchar (permissive_identchar | digitchar)*

rule token = parse
  [' ' '\012' '\t' '\r' '\n'] { token lexbuf }
| '{' { LBRACE }
| '}' { RBRACE }
| "->" { ARROW }
| "else" { ELSE }
| "true" { VAL(Bool, BoolConst true) }
| "false" { VAL(Bool, BoolConst false) }
| ['0'-'9']+ as lxm { VAL(Int, IntConst (int_of_string lxm)) }
| "(- " (['0'-'9']+ as lxm) ')' { VAL(Int, IntConst (-1 * (int_of_string lxm))) }
| "#unspecified" { UNSPEC }
| (ident as srt) "!val!" (digitchar+ as num) { VAL(to_sort srt, FreeSym (srt ^ "!" ^ num,0)) }
| ident as name (('_' digitchar+)? as num) ('$' digitchar+)? ("!" digitchar+)?
    { (* simple version: drop the $x which indcates the type *)
      let version = match num with
        | "" -> 0
        | v -> int_of_string (String.sub v 1 ((String.length v) -1))
      in
        SYMBOL(to_symbol (name, version))
    }
| eof { EOF }

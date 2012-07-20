{
open ParseModel
}

let digitchar = ['0'-'9']
let identchar = ['a'-'z' 'A'-'Z' '_' '!']
let ident = identchar (identchar | digitchar)*

rule token = parse
  [' ' '\t' '\n'] { token lexbuf }
| '{' { LBRACE }
| '}' { RBRACE }
| "->" { ARROW }
| "else" { ELSE }
| "true" { BOOL true }
| "false" { BOOL false }
| "#unspecified" { UNSPEC }
| ident as name '_' (digitchar+ as num) { IDENT(name, int_of_string num) }
| ident "!" (digitchar+ as num) { ELEM(int_of_string num) }
| ident as name { IDENT(name, 0) }
| eof { EOF }

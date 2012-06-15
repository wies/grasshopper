{
open ParseMSATForm
}

let digitchar = ['0'-'9']
let identchar = ['a'-'z' 'A'-'Z' '_']
let ident = identchar (identchar | digitchar)*

rule token = parse
  [' ' '\t'] { token lexbuf }
| '\n' { EOL }
| '=' { EQ }
| '(' { LPAREN }
| ')' { RPAREN }
| ',' { COMMA }
| '&' { AND }
| '|' { OR }
| '*' { STAR }
| ":=" { COLONEQ }
| ":" { COLON }
| "->" { ARROW }
| "!" { NOT }
| "DEFINE" { DEFINE }
| "FORMULA" { FORMULA }
| "VAR" { VAR }
| digitchar+ as num { NUM (int_of_string num) }
| ident as name '_' (digitchar+ as num) { IDENT (name, int_of_string num) }
| ident as name { NAME name }
| eof { EOF }

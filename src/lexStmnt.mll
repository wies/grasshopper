{
open ParseStmnt
}

let digitchar = ['0'-'9']
let lcidchar = ['a'-'z''_']
let ucidchar = ['A'-'Z']
let tident = lcidchar (lcidchar | ucidchar | digitchar)*
let pident = ucidchar (lcidchar | ucidchar | digitchar)*

rule token = parse
  [' ' '\t' '\n'] { token lexbuf }
| '=' { EQ }
| "~=" { NEQ }
| ":=" { COLONEQ}
| '|' { OR }
| '&' { AND }
| '~' { NOT }
| '(' { LPAREN }
| ')' { RPAREN }
| ':' { COLON }
| ';' { SEMICOLON }
| "assume" { ASSUME }
| "new" { NEW }
| "True" { TRUE }
| "False" { FALSE }
| tident as name { TIDENT(name) }
| pident as name { PIDENT(name) }
| eof { EOF }

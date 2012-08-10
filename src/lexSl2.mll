{
open ParseSl2
}

let digitchar = ['0'-'9']
let lcidchar = ['a'-'z''_']
let ucidchar = ['A'-'Z']
let tident = lcidchar (lcidchar | ucidchar | digitchar)*
let pident = ucidchar (lcidchar | ucidchar | digitchar)*

rule token = parse
  [' ' '\t' '\n'] { token lexbuf }
| "//" [^ '\n']* {token lexbuf }
| '=' { EQ }
| "~=" { NEQ }
| "||" { OR }
| "&&" { AND }
| '~' { NOT }
| '(' { LPAREN }
| ')' { RPAREN }
| ":=" { COLONEQ }
| ':' { COLON }
| ';' { SEMICOLON }
| ',' { COMMA }
| '.' { DOT }
| '*' { SEP }
| "|->" { PTS }
| "lseg" { LS }
(*| "assume" { ASSUME }*)
| "next" { NEXT }
| "new" { NEW }
| "free" { DISPOSE }
| "true" { TRUE }
| "false" { FALSE }
| "emp" { EMP }
| "Pre" { PRE }
| "Updates" { UPD }
| "Post" { POST }
| tident as name { TIDENT(name) }
| pident as name { PIDENT(name) }
| eof { EOF }

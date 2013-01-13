{
open ParseSl
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
| ',' { COMMA }
| '*' { SEP }
| "|->" { PTS }
| "|<-" { BPTS }
| "lseg" { LS }
| "dlseg" { DLS }
| "true" { TRUE }
| "false" { FALSE }
| "emp" { EMP }
| tident as name { TIDENT(name) }
| pident as name { PIDENT(name) }
| eof { EOF }

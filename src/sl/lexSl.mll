{
open ParseSl
}

let digitchar = ['0'-'9']
let lcidchar = ['a'-'z''_']
let ucidchar = ['A'-'Z']
let tident = lcidchar (lcidchar | ucidchar | digitchar)*
let pident = ucidchar (lcidchar | ucidchar | digitchar)*
let literal = digitchar+

rule token = parse
  [' ' '\t' '\n'] { token lexbuf }
| "//" [^ '\n']* {token lexbuf }
| '=' { EQ }
| "~=" { NEQ }
| "<=" { LEQ }
| ">=" { GEQ }
| "<" { LT }
| ">" { GT }
| "||" { OR }
| "&&" { AND }
| '~' { NOT }
| '.' { DOT }
| '(' { LPAREN }
| ')' { RPAREN }
| ',' { COMMA }
| '*' { SEP }
| '+' { PLUS }
| '-' { MINUS }
| '/' { DIV }
| "|->" { PTS }
| "|<-" { BPTS }
| "true" { TRUE }
| "false" { FALSE }
| "next" { NEXT }
| "back" { PREV }
| "data" { DATA }
| "emp" { EMP }
| "null" { NULL }
| tident as name { TIDENT(name) }
| pident as name { PIDENT(name) }
| literal as lit { INT (int_of_string lit) }
| eof { EOF }

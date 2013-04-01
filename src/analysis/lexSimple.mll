{
open ParseSimple
}

let digitchar = ['0'-'9']
let lcidchar = ['a'-'z''_']
let ucidchar = ['A'-'Z']
let tident = lcidchar (lcidchar | ucidchar | digitchar)*
let pident = ucidchar (lcidchar | ucidchar | digitchar)*

rule token = parse
  [' ' '\t' '\n'] { token lexbuf }
| "//" [^ '\n']* {token lexbuf }
| "==" { EQ }
| "!=" { NEQ }
| "<=" { LEQ }
| ">=" { GEQ }
| "<" { LT }
| ">" { GT }
| "||" { OR }
| "&&" { AND }
| '!' { NOT }
| '(' { LPAREN }
| ')' { RPAREN }
| '{' { LBRACKET }
| '}' { RBRACKET }
| ":=" { COLONEQ }
| ';' { SEMICOLON }
| ',' { COMMA }
| '.' { DOT }
| '*' { SEP }
| "|->" { PTS }
| "|<-" { BPTS }
| "lseg" { LS }
| "slseg" { SLS }
| "dlseg" { DLS }
| "assume" { ASSUME }
| "method" { PROCEDURE }
| "requires" { REQUIRES }
| "ensures" { ENSURES }
| "invariant" { INVARIANT }
| "return" { RETURN }
| "assert" { ASSERT }
| "next" { NEXT }
| "back" { PREV }
| "new" { NEW }
| "free" { DISPOSE }
| "if" { IF }
| "else" { ELSE }
| "while" { WHILE }
| "true" { TRUE }
| "false" { FALSE }
| "emp" { EMP }
| "null" { NULL }
| tident as name { TIDENT(name) }
| pident as name { PIDENT(name) }
| eof { EOF }

{
open ParseDef
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
| "==" { EQ }
| "!=" { NEQ }
| "<=" { LEQ }
| ">=" { GEQ }
| "<" { LT }
| ">" { GT }
| "||" { OR }
| "&&" { AND }
| "==>" { IMPLIES }
| "<=>" { EQUIV }
| '!' { NOT }
| '.' { DOT }
| '(' { LPAREN }
| ')' { RPAREN }
| '{' { LCBRK }
| '}' { RCBRK }
| ',' { COMMA }
| "*" { MULT }
| '+' { PLUS }
| '-' { MINUS }
| '/' { DIV }
| "in" { IN }
| "btwn" { BTWN }
| "reachWO" { REACHWO }
| "reach" { REACH }
| "forall" { FORALL }
| "exits" { EXISTS }
| "true" { TRUE }
| "false" { FALSE }
| "null" { NULL }
| ':' { COLON }
| "set" { SET_T }
| "fld" { FLD_T }
| "loc" { LOC_T }
| "int" { INT_T }
| "bool" { BOOL_T }
| tident as name { TIDENT(name) }
| pident as name { PIDENT(name) }
| literal as lit { INT (int_of_string lit) }
| eof { EOF }

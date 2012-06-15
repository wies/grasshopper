{
open ParseSmtLib
}

let digitchar = ['0'-'9']
let identchar = ['a'-'z' 'A'-'Z' '_' '!']
let ident = identchar (identchar | digitchar)*

rule token = parse
  [' ' '\t' '\n'] { token lexbuf }
| '(' { LPAREN }
| ')' { RPAREN }
| "\"model\""  { MODEL }
| "sat"  { SAT }
| "unsat"  { UNSAT }
| "unknown"  { UNKNOWN }
| "error" { ERROR }
| '\"' ([^'\"']* as str) '\"' { STRING(str) }


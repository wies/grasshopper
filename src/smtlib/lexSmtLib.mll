{
open ParseSmtLib
}

let digitchar = ['0'-'9']
let identchar = ['a'-'z' 'A'-'Z' '_' '!' '.']
let ident = identchar (identchar | digitchar)*

rule token = parse
  [' ' '\t' '\n'] { token lexbuf }
| '(' { LPAREN }
| ')' { RPAREN }
| '=' { EQ }
| "\"model\""  { MODEL }
| "sat"  { SAT }
| "unsat"  { UNSAT }
| "unknown"  { UNKNOWN }
| "error" { ERROR }
| "and" { AND }
| "or" { OR }
| "not" { NOT }
| "let" { LET }
| "true" { TRUE }
| "false" { FALSE }
| '\"' ([^'\"']* as str) '\"' { STRING(str) }
| digitchar+ as num { NUM (int_of_string num) }
| ident as name '_' (digitchar+ as num) { IDENT (name, int_of_string num) }
| ident as name { IDENT(name, 0) }


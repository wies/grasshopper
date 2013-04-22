{
open ParseProg

let keyword_table = Hashtbl.create 32
let _ =
  List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
    ([("assert", ASSERT),
      ("assume", ASSUME),
      ("bool", BOOL),
      ("else", ELSE),
      ("emp", EMP),
      ("ensures", ENSURES),
      ("false", FALSE),
      ("free", DISPOSE),
      ("ghost", GHOST),
      ("if", IF),
      ("int", INT),
      ("invariant", INVARIANT),
      ("new", NEW),
      ("null", NULL),
      ("procedure", PROCEDURE),
      ("requires", REQUIRES),
      ("return", RETURN),
      ("returns", RETURNS),
      ("struct", STRUCT),
      ("true", TRUE),
      ("var", VAR),
      ("while", WHILE),
   ])
}

let digitchar = ['0'-'9']
let idchar = ['A'-'Z''a'-'z''_']
let ident = idchar (idchar | digitchar)*
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
| '!' { NOT }
| '+' { PLUS }
| '-' { MINUS }
| '/' { DIV }
| '*' { MULT }
| '(' { LPAREN }
| ')' { RPAREN }
| '{' { LBRACKET }
| '}' { RBRACKET }
| ":=" { COLONEQ }
| ';' { SEMICOLON }
| ',' { COMMA }
| '.' { DOT }
| "&*&" { SEP }
| "|->" { PTS }
| ident as kw
    { try
        Hashtbl.find keyword_table kw
      with Not_found ->
        IDENT (kw)
    }
| literal as lit { INT (int_of_string lit) }
| eof { EOF }

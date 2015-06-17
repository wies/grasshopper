{
open ModelParser

}

let digitchar = ['0'-'9']
let identchar = ['a'-'z' 'A'-'Z' '?' '$' '.' '@' '_' '#']
let ident = identchar (identchar | digitchar | ':' | '-' | '!')*
let ws       = [' ' '\009' '\012']

rule token = parse
    ['\r' '\t' '\n']     { token lexbuf } (* skip whitespace *)
  | ws                  { token lexbuf }
  | ident as name       { IDENT name }
  | digitchar digitchar* as num { NUM (int_of_string num) }
  | ':'                 { COLON }
  | ','                 { COMMA }
  | '('                 { LPAREN }
  | ')'                 { RPAREN }
  | '['                 { LBRACK }
  | ']'                 { RBRACK }
  | eof			{ EOF }
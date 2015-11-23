{
open Grass
open Prog
open SplParser
open Lexing

(* set file name *)
let set_file_name lexbuf name =
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = name }


let keyword_table = Hashtbl.create 32
let _ =
  List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
    ([("Array", ARRAY);
      ("ArrayCell", ARRAYCELL);
      ("assert", ASSERT);
      ("assume", ASSUME);
      ("Bool", BOOL);
      ("comment", COMMENT);
      ("else", ELSE);
      ("emp", EMP);
      ("ensures", ENSURES);
      ("false", BOOLVAL(false));
      ("forall", QUANT(SplSyntax.Forall));
      ("exists", QUANT(SplSyntax.Exists));
      ("footprint", FOOTPRINT);
      ("free", FREE);
      ("function", FUNCTION);
      ("ghost", GHOST);
      ("havoc", HAVOC);
      ("if", IF);
      ("in", IN);
      ("Int", INT);
      ("Byte", BYTE);
      ("invariant", INVARIANT);
      ("include", INCLUDE);
      ("implicit", IMPLICIT);
      ("Loc", LOC);
      ("Map", MAP);
      ("matching", MATCHING);
      ("new", NEW);
      ("null", NULL);
      ("outputs", OUTPUTS);
      ("pattern", PATTERN);
      ("predicate", PREDICATE);
      ("procedure", PROCEDURE);
      ("pure", PURE);
      ("requires", REQUIRES);
      ("return", RETURN);
      ("returns", RETURNS);
      ("struct", STRUCT);
      ("subsetof", LEQ);
      ("Set", SET);
      ("true", BOOLVAL(true));
      ("var", VAR);
      ("while", WHILE);
      ("without", WITHOUT);
      ("yields", YIELDS);
      ("axiom", AXIOM);
      ("int2byte", INT2BYTE);
      ("byte2int", BYTE2INT);
   ])

let lexical_error lexbuf msg =
  let pos = lexeme_start_p lexbuf in 
  let spos = 
    { sp_file = pos.pos_fname;
      sp_start_line = pos.pos_lnum;
      sp_start_col = pos.pos_cnum - pos.pos_bol;
      sp_end_line = pos.pos_lnum;
      sp_end_col = pos.pos_cnum - pos.pos_bol;
    } 
  in
  ProgError.syntax_error spos msg

let hexa_to_int num =
  let rec process acc i =
    if i >= String.length num then acc
    else
      begin
        let d = match num.[i] with
          | '0' -> 0    | '1' -> 1  | '2' -> 2
          | '3' -> 3    | '4' -> 4  | '5' -> 5
          | '6' -> 6    | '7' -> 7  | '8' -> 8
          | '9' -> 9    | 'A' | 'a' -> 10
          | 'B' | 'b' -> 11   | 'C' | 'c' -> 12
          | 'D' | 'd' -> 13   | 'E' | 'e' -> 14
          | 'F' | 'f' -> 15
          | _ -> failwith "hexa_to_int: should not happen."
        in
        let acc2 = 
          Int64.add
            (Int64.shift_left acc 4)
            (Int64.of_int d)
        in
        process acc2 (i+1)
      end
  in
  process Int64.zero 0
}

let digitchar = ['0'-'9']
let idchar = ['A'-'Z''a'-'z''_']
let ident = idchar (idchar | digitchar)*
let digits = digitchar+

rule token = parse
    [' ' '\t'] { token lexbuf }
| '\n' { Lexing.new_line lexbuf; token lexbuf }
| "//" [^ '\n']* { token lexbuf }
| "/*" { comments 0 lexbuf }
| "\"" ([^ '"']* as str) "\"" { STRINGVAL str }
| "==>" { IMPLIES }
| "<=>" { IFF }
| "==" { EQ }
| "!=" { NEQ }
| "<=" { LEQ }
| ">=" { GEQ }
| '=' { EQ }
| "<" { LT }
| ">" { GT }
| "||" { OR }
| "&&" { AND }
| "!in" { NOTIN }
| '!' { NOT }
| "**-" { lexical_error lexbuf (Some "Unknown operator. Did you mean '-**'?") }
| "-**" { SEPINCL }
| "++" { UNION }
| "--" { DIFF }
| "**" { INTER }
| '@' { AT }
| '+' { PLUS }
| '-' { MINUS }
| '/' { DIV }
| '*' { TIMES }
| '(' { LPAREN }
| ')' { RPAREN }
| '{' { LBRACE }
| '}' { RBRACE }
| '[' { LBRACKET }
| ']' { RBRACKET }
| ":=" { COLONEQ }
| "::" { COLONCOLON }
| ':' { COLON }
| ';' { SEMICOLON }
| ',' { COMMA }
| '.' { DOT }
| "&*&" { SEPSTAR }
| "&+&" { SEPPLUS }
| "|->" { PTS }
| '&' { BAND }
| '|' { BOR }
| '~' { BNOT }
| "<-<" { BSL }
| ">->" { BSR }
| ident as kw
    { try
        Hashtbl.find keyword_table kw
      with Not_found ->
        IDENT (kw)
    }
| "0x" (['A'-'F''a'-'f''0'-'9']+ as num) { INTVAL (hexa_to_int num) }
| digits as num { INTVAL (Int64.of_string num) }
| "'" (_ as c) "'" { CHARVAL c }
| eof { EOF }
| _ { lexical_error lexbuf None }

and comments level = parse
| "*/" { if level = 0 then token lexbuf
         else comments (level - 1) lexbuf
       }
| "/*" { comments (level + 1) lexbuf }
| '\n' { Lexing.new_line lexbuf; comments (level) lexbuf }
| _ { comments level lexbuf }
| eof { EOF }

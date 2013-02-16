%{
open Form
open ParseSmtLibAux
open Axioms

let parse_error = ParseError.parse_error
%}

%token <int> NUM
%token <string * int> IDENT
%token <string> STRING
%token LPAREN RPAREN LBRACE RBRACE QUOTE ARROW EQ
%token SAT UNSAT UNKNOWN ERROR MODEL LET AND OR NOT 
%token FALSE TRUE
%start main
%type <ParseSmtLibAux.smtlib_answer> main
%%

main:
  SAT { SmtSat }
| UNSAT { SmtUnsat }
| UNKNOWN { SmtUnknown }
| rmodel { SmtModel $1 }
| rerror { SmtError $1 }
;
    
rerror:
  LPAREN ERROR STRING RPAREN { $3 }
;

rmodel:
  LPAREN LPAREN MODEL STRING RPAREN RPAREN 
    { ParseError.input := Some $4;
      let buff = Lexing.from_string $4 in
      ParseError.buffer := Some buff;
      ParseModel.main LexModel.token buff }
| STRING 
    { ParseError.input := Some $1;
      let buff = Lexing.from_string $1 in
      ParseError.buffer := Some buff;
      ParseModel.main LexModel.token buff }
;




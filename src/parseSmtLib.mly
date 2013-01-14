%{
open Form
open ParseSmtLibAux
open Axioms

(*let parse_error = ParseError.parse_error*)
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
| form { let res = SmtForm $1 in clear_tables (); res }
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

terms:
| term terms { $1 :: $2 }
| term { [$1] }

term:
| IDENT { resolve_id_to_term $1 }
| LPAREN IDENT terms RPAREN { mk_app $2 $3 }
;

binding:
| LPAREN LPAREN IDENT ferm RPAREN RPAREN { add_def $3 $4 }

forms:
| form forms { $1 :: $2 }
| form { [$1] }

form:
| LPAREN LET binding form RPAREN { $4 }
| LPAREN AND forms RPAREN { mk_and $3 }
| LPAREN OR forms RPAREN { mk_or $3 }
| LPAREN NOT form RPAREN { mk_not $3 }
| LPAREN EQ term term RPAREN { mk_eq $3 $4 }
| LPAREN IDENT terms RPAREN { mk_pred $2 $3 }
| IDENT { resolve_id_to_form $1 }
| FALSE { mk_false }
| TRUE { mk_true }
;

ferm:
| LPAREN AND forms RPAREN { (Some (mk_and $3), None) }
| LPAREN OR forms RPAREN { (Some (mk_or $3), None) }
| LPAREN NOT form RPAREN { (Some (mk_not $3), None) }
| LPAREN EQ term term RPAREN { (Some (mk_eq $3 $4), None) }
| LPAREN IDENT terms RPAREN { (Some (mk_pred $2 $3), Some (mk_app $2 $3)) }
| IDENT { (Some (resolve_id_to_form $1), Some (resolve_id_to_term $1)) }
| FALSE { (Some mk_false, None) }
| TRUE { (Some mk_true, None) }


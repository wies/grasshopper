%{
open Form
open ParseSmtLibAux


%}

%token <string> STRING
%token LPAREN RPAREN LBRACE RBRACE QUOTE ARROW
%token SAT UNSAT UNKNOWN ERROR MODEL 
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
    { let buff = Lexing.from_string $4 in
      ParseModel.main LexModel.token buff }
;


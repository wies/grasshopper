%{
open Form
open Stmnt

let parse_error = ParseError.parse_error

%}

%token <string> TIDENT
%token <string> PIDENT
%token EQ
%token LPAREN RPAREN COLON SEMICOLON
%token EQ NEQ COLONEQ 
%token ASSUME NEW DISPOSE TRUE FALSE
%token AND OR NOT
%token EOF

%left SEMICOLON
%left OR
%left AND
%right NOT

%nonassoc EQ 
%nonassoc NEQ 
%nonassoc COLON 
%nonassoc COLONEQ 
%nonassoc ASSUME NEW DISPOSE
%nonassoc TRUE FALSE

%start main
%type <Stmnt.path> main
%%

main:
  path  { $1 }
;


path:
  stmnt path EOF { $1 :: $2 }
| stmnt EOF { [$1] }
;

stmnt:
| ASSUME form SEMICOLON { Assume $2 }
| NEW TIDENT SEMICOLON { New (mk_ident $2) }
| DISPOSE TIDENT SEMICOLON { Dispose (mk_ident $2) }
| TIDENT COLONEQ term SEMICOLON { VarUpdate (mk_ident $1, $3) }
| TIDENT term COLONEQ term SEMICOLON {FunUpdate (mk_ident $1, $2, $4) }
| TIDENT COLON { Label $1 }
;

term:
| TIDENT args { mk_app (mk_ident $1) $2 }
| TIDENT { mk_const (mk_ident $1) }
| LPAREN term RPAREN { $2 }
;

subterm:
| TIDENT {mk_const (mk_ident $1)}
| LPAREN TIDENT args RPAREN { mk_app (mk_ident $2) $3 }
| LPAREN subterm RPAREN { $2 }

args:
  subterm { [$1] }
| subterm args { $1 :: $2 }
;

form:
| LPAREN form RPAREN { $2 }
| NOT form { mk_not $2 }
| form AND form { mk_and [$1; $3] }
| form OR form { mk_or [$1; $3] }
| atom { $1 }
;

atom:
| TRUE { mk_true }
| FALSE { mk_false }
| term EQ term { mk_eq $1 $3 }
| term NEQ term { mk_not (mk_eq $1 $3) }
| PIDENT args { mk_pred (mk_ident $1) $2 }
;

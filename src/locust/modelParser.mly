%{
  open Lexing
%}

%token <string> IDENT
%token <int> NUM
%token COLON COMMA 
%token LPAREN RPAREN LBRACK RBRACK
%token EOF

%start heap
%type <((string * int) list * (int * string * int) list)> heap
%%

heap:
  varList fieldList { ($1, $2) }

varList:
    varDef { [ $1 ] }
  | varDef varList { $1 :: $2 }

fieldList:
    pointsToDef { [ $1 ] }
  | pointsToDef fieldList { $1 :: $2 }

varDef:
    LBRACK IDENT COLON NUM RBRACK { ($2, $4) }

pointsToDef:
    LPAREN NUM COMMA IDENT COMMA NUM RPAREN { ($2, $4, $6) }

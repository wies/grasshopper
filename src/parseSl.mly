%{
open Sl

%}

%token <string> TIDENT
%token <string> PIDENT
%token LPAREN RPAREN
%token EQ NEQ
%token PTS LS TRUE FALSE
%token SEP AND OR NOT
%token EOF

%left OR
%left AND
%left SEP
%right NOT

%nonassoc EQ 
%nonassoc NEQ 
%nonassoc PTS LS
%nonassoc TRUE FALSE

%start main
%type <sl_form> main
%%

main:
  pure spatial EOF { ($1, $2) }
;

term:
| TIDENT { mk_ident $1 }
| LPAREN term RPAREN { $2 }
;

pure:
| TRUE { mk_true }
| FALSE { mk_false }
| term EQ term { mk_eq $1 $3 }
| term NEQ term { mk_not (mk_eq $1 $3) }
| NOT pure { mk_not $2 }
| pure AND pure { mk_and [$1; $3] }
| pure OR pure { mk_or [$1; $3] }
| LPAREN pure RPAREN { $2 }
;

spatial:
| term PTS term { mk_pts $1 $3 }
| LS term term { mk_ls $2 $3 }
| spatial OR spatial { mk_disj [$1; $3] }
| spatial AND spatial { mk_conj [$1; $3] }
| spatial SEP spatial { mk_sep [$1; $3] }
| LPAREN spatial RPAREN { $2 }
| EMP { Emp }
;

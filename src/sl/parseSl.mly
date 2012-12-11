%{
open Sl

%}

%token <string> TIDENT
%token <string> PIDENT
%token LPAREN RPAREN
%token EQ NEQ
%token PTS LS TRUE FALSE EMP
%token SEP AND OR NOT
%token COMMA EOF

%left OR
%left AND
%left SEP
%right NOT

%nonassoc EQ 
%nonassoc NEQ 
%nonassoc PTS LS
%nonassoc TRUE FALSE

%start main
%type <Sl.sl_form> main
%%

main:
  pure spatial EOF { ($1, $2) }
;

term:
| TIDENT { mk_ident $1 }
| LPAREN term RPAREN { $2 }
;

pure:
| TRUE { Pure.mk_true }
| FALSE { Pure.mk_false }
| term EQ term { Pure.mk_eq $1 $3 }
| term NEQ term { Pure.mk_not (Pure.mk_eq $1 $3) }
| NOT pure { Pure.mk_not $2 }
| pure AND pure { Pure.mk_and [$1; $3] }
| pure OR pure { Pure.mk_or [$1; $3] }
| LPAREN pure RPAREN { $2 }
;

spatial:
| term PTS term { Spatial.mk_pts $1 $3 }
| LS LPAREN term COMMA term RPAREN { Spatial.mk_ls $3 $5 }
| spatial OR spatial { Spatial.mk_disj [$1; $3] }
| spatial AND spatial { Spatial.mk_conj [$1; $3] }
| spatial SEP spatial { Spatial.mk_sep [$1; $3] }
| LPAREN spatial RPAREN { $2 }
| EMP { Spatial.Emp }
;

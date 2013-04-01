%{
open Sl

let parse_error = ParseError.parse_error

%}

%token <string> TIDENT
%token <string> PIDENT
%token LPAREN RPAREN
%token EQ NEQ
%token PTS BPTS LS SLS DLS TRUE FALSE EMP
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
%type <Sl.form> main
%%

main:
  form EOF { $1 }
;

term:
| TIDENT { mk_ident $1 }
| LPAREN term RPAREN { $2 }
;

form:
| TRUE { mk_true }
| FALSE { mk_false }
| EMP { Emp }
| term EQ term { mk_eq $1 $3 }
| term NEQ term { mk_not (mk_eq $1 $3) }
| term PTS term { mk_pts $1 $3 }
| term BPTS term { mk_prev_pts $1 $3 }
| SLS LPAREN term COMMA term RPAREN { mk_sls $3 $5 }
| LS LPAREN term COMMA term RPAREN { mk_ls $3 $5 }
| DLS LPAREN term COMMA term COMMA term COMMA term RPAREN { mk_dls $3 $5 $7 $9 }
| NOT form { mk_not $2 }
| form AND form { mk_and $1 $3 }
| form OR form { mk_or $1 $3 }
| form SEP form { mk_sep $1 $3 }
| LPAREN form RPAREN { $2 }
;


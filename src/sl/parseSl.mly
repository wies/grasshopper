%{
open Sl

let parse_error = ParseError.parse_error

%}

%token <string> TIDENT
%token <string> PIDENT
%token <int> INT
%token LPAREN RPAREN
%token EQ NEQ LEQ GEQ LT GT
%token PTS BPTS TRUE FALSE EMP
%token NEXT PREV DATA NULL
%token SEP AND OR NOT
%token PLUS MINUS DIV
%token COMMA EOF DOT

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

pterm:
| pterm DOT NEXT { FormUtil.mk_read fpts $1 }
| pterm DOT PREV { FormUtil.mk_read fprev_pts $1 }
| pterm DOT DATA { FormUtil.mk_read fdata $1 }
| pterm PLUS pterm { FormUtil.mk_plus $1 $3 }
| pterm MINUS pterm { FormUtil.mk_minus $1 $3 }
/*| pterm SEP pterm { FormUtil.mk_mult $1 $3 }*/
| pterm DIV pterm { FormUtil.mk_div $1 $3 }
| MINUS pterm { FormUtil.mk_uminus $2 }
| TIDENT { FormUtil.mk_free_const (mk_ident $1) }
| NULL { FormUtil.mk_null }
| INT { FormUtil.mk_int $1 }
| LPAREN pterm RPAREN { $2 }
;

argst:
| pterm { [$1] }
| pterm COMMA argst { $1 :: $3 }
| /* empty */ { [] }
;

form:
/* pure part */
| TRUE { mk_true }
| FALSE { mk_false }
| pterm EQ pterm { mk_pure (FormUtil.mk_eq $1 $3) }
| pterm NEQ pterm { mk_pure (FormUtil.mk_neq $1 $3) }
| pterm LT pterm { mk_pure (FormUtil.mk_lt $1 $3) }
| pterm GT pterm { mk_pure (FormUtil.mk_gt $1 $3) }
| pterm LEQ pterm { mk_pure (FormUtil.mk_leq $1 $3) }
| pterm GEQ pterm { mk_pure (FormUtil.mk_geq $1 $3) }
/* spatial part */
| EMP { mk_emp }
| pterm PTS pterm { mk_pts $1 $3 }
| pterm BPTS pterm { mk_prev_pts $1 $3 }
| TIDENT LPAREN argst RPAREN { mk_spatial_pred $1 $3 }
/* boolean structure */
| NOT form { mk_not $2 }
| form AND form { mk_and $1 $3 }
| form OR form { mk_or $1 $3 }
| form SEP form { mk_sep $1 $3 }
| LPAREN form RPAREN { $2 }
;


%{
open Form
open FormUtil

let parse_error = ParseError.parse_error

%}

%token <string> TIDENT
%token <string> PIDENT
%token <int> INT
%token EQ NEQ LEQ GEQ LT GT
%token OR AND IMPLIES EQUIV NOT
%token DOT LPAREN RPAREN COMMA COLON LCBRK RCBRK
%token MULT PLUS MINUS DIV
%token REACHWO BTWN REACH IN
%token FORALL EXISTS TRUE FALSE
%token SET_T FLD_T LOC_T INT_T BOOL_T
%token NULL EOF

%left OR
%left AND
%left SEP
%right NOT

%start main
%type <(string * ((Form.ident * Form.sort) list) * Form.form * Form.form) list> main
%%

tpe:
  FLD_T tpe { Fld $2 }
| SET_T tpe { Set $2 }
| BOOL_T { Bool }
| INT_T { Int }
| LOC_T { Loc }
;


typed_args:
  TIDENT COLON tpe COMMA typed_args { (mk_ident $1, $3) :: $5 }
| TIDENT COLON tpe { (mk_ident $1, $3) :: [] }
| /* empty */ { [] }
;


term:
| term PLUS  term { mk_plus $1 $3 }
| term MINUS term { mk_minus $1 $3 }
| term MULT  term { mk_mult $1 $3 }
| term DIV   term { mk_div $1 $3 }
| MINUS term      { mk_uminus $2 }
| term LPAREN term RPAREN { mk_read $1 $3 }
| TIDENT          { mk_free_const (mk_ident $1) }
| NULL            { mk_null }
| INT             { mk_int $1 }
| LCBRK term_args RCBRK { mk_setenum $2 }
| LPAREN term RPAREN { $2 }
;


term_args:
  term COMMA term_args { $1 :: $3 }
| term { $1 :: [] }
| /* empty */ { [] }
;


f_binop:
  EQ   { mk_eq }
| NEQ  { mk_neq }
| LEQ  { mk_leq }
| GEQ  { mk_geq }
| LT   { mk_lt }
| GT   { mk_gt }
| IN   { mk_elem }
;


form:
| LPAREN form RPAREN { $2 }
| TRUE { mk_true }
| FALSE { mk_false }
| BTWN LPAREN term COMMA term COMMA term RPAREN { mk_btwn Sl.fpts $3 $5 $7 }
| REACH LPAREN term COMMA term RPAREN { mk_reach Sl.fpts $3 $5 }
| term f_binop term { $2 $1 $3 }
| NOT form { mk_not $2 }
| form OR  form { mk_or  [$1; $3] }
| form AND form { mk_and [$1; $3] }
| form IMPLIES form { mk_implies $1 $3 }
| form EQUIV form { mk_iff $1 $3 }
| FORALL typed_args DOT form { mk_forall $2 $4 }
| EXISTS typed_args DOT form { mk_exists $2 $4 }
;

def:
TIDENT LPAREN typed_args RPAREN LCBRK form COMMA form RCBRK { ($1, $3, $6, $8) }
;

main:
  def main { $1 :: $2 }
| EOF { [] };

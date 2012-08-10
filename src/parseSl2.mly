%{
open Sl
open Stmnt

let parse_error = ParseStmntAux.parse_error

%}

%token <string> TIDENT
%token <string> PIDENT
%token LPAREN RPAREN COLON SEMICOLON DOT
%token EQ NEQ
%token PTS LS TRUE FALSE EMP
%token COLONEQ /*ASSUME*/ NEW NEXT DISPOSE
%token SEP AND OR NOT COMMA
%token PRE UPD POST
%token EOF

%left OR
%left AND
%left SEP
%left DOT
%right NOT
%left SEMICOLON

%nonassoc EQ 
%nonassoc NEQ 
%nonassoc PTS LS
%nonassoc TRUE FALSE
%nonassoc COLON 
%nonassoc COLONEQ 
%nonassoc /*ASSUME*/ NEW DISPOSE

%token <string> TIDENT
%token <string> PIDENT

%start main
%type <Sl.sl_form * Stmnt.path * Sl.sl_form> main
%%

main:
  PRE form UPD path POST form { ($2, $4, $6) }
;

form: 
  pure spatial { ($1, $2) }
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

path:
  stmnt path { $1 :: $2 }
| /* empty */ { [] }
;

stmnt:
| NEW TIDENT SEMICOLON { New (mk_ident $2) }
| DISPOSE TIDENT SEMICOLON { Dispose (mk_ident $2) }
| pterm COLONEQ pterm SEMICOLON   { match $1 with
                                    | Form.Const id -> VarUpdate (id, $3)
                                    | Form.FunApp (id, [arg]) -> FunUpdate (id, arg, $3)
                                    | _ -> failwith "pterm rule returned something strange"
                                  }
| TIDENT COLON { Label $1 }
;

pterm:
| TIDENT DOT NEXT { Form.mk_app pts [Form.mk_const (mk_ident $1)] }
| TIDENT { Form.mk_const (mk_ident $1) }
| LPAREN pterm RPAREN { $2 }
;


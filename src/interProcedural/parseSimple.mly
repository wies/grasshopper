%{
open Sl
open Stmnt

let parse_error = ParseStmntAux.parse_error

%}

%token <string> TIDENT
%token <string> PIDENT
%token LPAREN RPAREN LBRACKET RBRACKET
%token SEMICOLON DOT
%token EQ NEQ
%token PTS LS TRUE FALSE EMP
%token COLONEQ
%token ASSUME ASSERT NEW NEXT DISPOSE RETURN
%token SEP AND OR NOT COMMA
%token IF ELSE WHILE
%token REQUIRES ENSURES
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
%nonassoc COLONEQ 
%nonassoc ASSUME ASSERT
%nonassoc NEW DISPOSE

%token <string> TIDENT
%token <string> PIDENT

%start main
%type <SimpleLanguage.procedure list> main
%%

main:
  procedure main { $1 :: $2 }
| /* empty */ { [] }
;

procedure:
  TIDENT LPAREN args RPAREN REQUIRES sl_form ENSURES sl_form LBRACKET path RBRACKET { { name = $1,
                                                                                        args = $3,
                                                                                        precondition = $6,
                                                                                        postcondition = $8,
                                                                                        body = $10} }
;

sl_form: 
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

args:
  TIDENT { [$1] }
| TIDENT COMMA args { $1 :: $3 }
| /* empty */ { [] }
;

path:
  stmnt path { $1 :: $2 }
| /* empty */ { [] }
;

stmnt:
| NEW TIDENT SEMICOLON { New (mk_ident $2) }
| DISPOSE TIDENT SEMICOLON { Dispose (mk_ident $2) }
| pterm COLONEQ rhs SEMICOLON { match $1 with
                                | Form.Const id -> VarUpdate (id, $3)
                                | Form.FunApp (id, [arg]) -> FunUpdate (id, arg, $3)
                                | _ -> failwith "pterm rule returned something strange"
                              }
| ASSUME sl_form SEMICOLON { Assume $2 }
| ASSERT sl_form SEMICOLON { Assert $2 }
| IF LPAREN expr RPAREN stmnt ELSE stmnt { Ite ($3, $5, $7) }
| WHILE LPAREN expr RPAREN sl_form LBRACKET path RBRACKET { While ($3, $5, $7) }
| RETURN pterm SEMICOLON { Return $2 }
| LBRACKET path RBRACKET { Block $2 }
;

rhs:
  pterm { Term $1 }
| TIDENT LPAREN argsCall RPAREN { Call ($1, $3) }

argsCall:
  pterm { [$1] }
| pterm COMMA argsCall { $1 :: $3 }
| /* empty */ { [] }
;

pterm:
| TIDENT DOT NEXT { Form.mk_app pts [Form.mk_const (mk_ident $1)] }
| TIDENT { Form.mk_const (mk_ident $1) }
| LPAREN pterm RPAREN { $2 }
;

expr:
| LPAREN expr RPAREN { $2 }
| NOT expr { mk_not $2 }
| expr AND expr { mk_and [$1; $3] }
| expr OR expr { mk_or [$1; $3] }
| atom { $1 }
;

atom:
| TRUE { mk_true }
| FALSE { mk_false }
| pterm EQ pterm { mk_eq $1 $3 }
| pterm NEQ pterm { mk_not (mk_eq $1 $3) }
| PIDENT args { mk_pred (mk_ident $1) $2 }
;

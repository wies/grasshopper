%{
open Sl
open Stmnt
open SimpleLanguage

let parse_error = ParseStmntAux.parse_error

%}

%token <string> TIDENT
%token <string> PIDENT
%token LPAREN RPAREN LBRACKET RBRACKET
%token SEMICOLON DOT
%token EQ NEQ
%token PTS BPTS LS DLS TRUE FALSE EMP
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
  TIDENT LPAREN args RPAREN REQUIRES sl_form ENSURES sl_form LBRACKET path RBRACKET { { name = mk_ident $1;
                                                                                        args = $3;
                                                                                        precondition = $6;
                                                                                        postcondition = $8;
                                                                                        body = Block $10} }
;

term:
| TIDENT { mk_ident $1 }
| LPAREN term RPAREN { $2 }
;

sl_form:
| TRUE { mk_true }
| FALSE { mk_false }
| EMP { Emp }
| term EQ term { mk_eq $1 $3 }
| term NEQ term { mk_not (mk_eq $1 $3) }
| term PTS term { mk_pts $1 $3 }
| term BPTS term { mk_prev_pts $1 $3 }
| LS LPAREN term COMMA term RPAREN { mk_ls $3 $5 }
| DLS LPAREN term COMMA term COMMA term COMMA term RPAREN { mk_dls $3 $5 $7 $9 }
| NOT sl_form { mk_not $2 }
| sl_form AND sl_form { mk_and $1 $3 }
| sl_form OR sl_form { mk_or $1 $3 }
| sl_form SEP sl_form { mk_sep $1 $3 }
| LPAREN sl_form RPAREN { $2 }
;

args:
  TIDENT { [mk_ident $1] }
| TIDENT COMMA args { (mk_ident $1) :: $3 }
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
| WHILE LPAREN expr RPAREN sl_form LBRACKET path RBRACKET { While ($3, $5, Block $7) }
| RETURN pterm SEMICOLON { Return $2 }
| call SEMICOLON { VarUpdate (Form.mk_ident "no_return", $1) }
| LBRACKET path RBRACKET { Block $2 }
;

rhs:
  pterm { Term $1 }
| call { $1 }

call:
| TIDENT LPAREN argsCall RPAREN { Call (mk_ident $1, $3) }

argsCall:
  pterm { [Term $1] }
| pterm COMMA argsCall { (Term $1) :: $3 }
| /* empty */ { [] }
;

pterm:
| TIDENT DOT NEXT { Form.mk_app pts [Form.mk_const (mk_ident $1)] }
| TIDENT { Form.mk_const (mk_ident $1) }
| LPAREN pterm RPAREN { $2 }
;

expr:
| LPAREN expr RPAREN { $2 }
| NOT expr { Form.mk_not $2 }
| expr AND expr { Form.mk_and [$1; $3] }
| expr OR expr { Form.mk_or [$1; $3] }
| atom { $1 }
;

atom:
| TRUE { Form.mk_true }
| FALSE { Form.mk_false }
| pterm EQ pterm { Form.mk_eq $1 $3 }
| pterm NEQ pterm { Form.mk_not (Form.mk_eq $1 $3) }
| PIDENT args { Form.mk_pred (mk_ident $1) (List.map (fun t -> Form.Const t) $2) }
;

%{
open Sl
open Stmnt
open SimpleLanguage

let parse_error = ParseError.parse_error

%}

%token <string> TIDENT
%token <string> PIDENT
%token LPAREN RPAREN LBRACKET RBRACKET
%token SEMICOLON DOT
%token EQ NEQ
%token PTS BPTS LS DLS TRUE FALSE EMP NULL
%token COLONEQ
%token ASSUME ASSERT NEW NEXT PREV DISPOSE RETURN
%token SEP AND OR NOT COMMA
%token IF ELSE WHILE
%token PROCEDURE REQUIRES ENSURES INVARIANT
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
  PROCEDURE TIDENT LPAREN args RPAREN proc_contract LBRACKET block RBRACKET 
  { { name = mk_ident $2;
      args = $4;
      precondition = fst $6;
      postcondition = snd $6;
      body = Block $8} 
  }
;

proc_contract:
| REQUIRES sl_form SEMICOLON proc_contract { (mk_sep $2 (fst $4), snd $4) }
| ENSURES sl_form SEMICOLON proc_contract { (fst $4, mk_sep $2 (snd $4)) }
| /* empty */ { (mk_emp, mk_emp) }

term:
| NULL { mk_ident "null" }
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

block:
  stmnt block { $1 :: $2 }
| /* empty */ { [] }
;

stmnt:
| NEW TIDENT SEMICOLON { New (mk_ident $2) }
| DISPOSE TIDENT SEMICOLON { Dispose (mk_ident $2) }
| pterm COLONEQ rhs SEMICOLON { match $1 with
                                | Form.App (Form.FreeSym id, [], _) -> VarUpdate (id, $3)
                                | Form.App (Form.Read, [Form.App (Form.FreeSym id, [], _); ind], _) -> FunUpdate (id, ind, $3)
                                | _ -> failwith "pterm rule returned something strange"
                              }
| ASSUME sl_form SEMICOLON { Assume $2 }
| ASSERT sl_form SEMICOLON { Assert ($2, None) }
| IF LPAREN expr RPAREN stmnt ELSE stmnt { Ite ($3, $5, $7) }
| IF LPAREN expr RPAREN stmnt { Ite ($3, $5, Block []) }
| WHILE LPAREN expr RPAREN loop_contract LBRACKET block RBRACKET { While ($3, $5, Block $7) }
| RETURN pterm SEMICOLON { Return $2 }
| call SEMICOLON { VarUpdate (FormUtil.mk_ident "no_return", $1) }
| LBRACKET block RBRACKET { Block $2 }
;

loop_contract:
  INVARIANT sl_form SEMICOLON loop_contract { mk_sep $2 $4 }
| /* empty */ { mk_emp }

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
| TIDENT DOT NEXT { FormUtil.mk_read fpts (mk_loc (mk_ident $1)) }
| TIDENT DOT PREV { FormUtil.mk_read fprev_pts (mk_loc (mk_ident $1)) }
| TIDENT { mk_loc (mk_ident $1) }
| NULL { FormUtil.mk_null }
| LPAREN pterm RPAREN { $2 }
;

expr:
| LPAREN expr RPAREN { $2 }
| NOT expr { FormUtil.mk_not $2 }
| expr AND expr { FormUtil.mk_and [$1; $3] }
| expr OR expr { FormUtil.mk_or [$1; $3] }
| atom { $1 }
;

atom:
| TRUE { FormUtil.mk_true }
| FALSE { FormUtil.mk_false }
| pterm EQ pterm { FormUtil.mk_eq $1 $3 }
| pterm NEQ pterm { FormUtil.mk_not (FormUtil.mk_eq $1 $3) }
| PIDENT args { FormUtil.mk_pred (mk_ident $1) (List.map (fun t -> (*FormUtil.mk_free_const*) mk_loc t) $2) }
;

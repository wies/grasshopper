%{
open Prog
open Grass
open SplSyntax
open Lexing


(* let parse_error =  ParseError.parse_error *)

let mk_position s e =
  let start_pos = Parsing.rhs_start_pos s in
  let end_pos = Parsing.rhs_end_pos e in
  { sp_file = start_pos.pos_fname;
    sp_start_line = start_pos.pos_lnum;
    sp_start_col = start_pos.pos_cnum - start_pos.pos_bol;
    sp_end_line = end_pos.pos_lnum;
    sp_end_col = end_pos.pos_cnum - end_pos.pos_bol;
  } 

let fix_scopes stmnt =
  let rec fs scope = function
    | LocalVars (decls, pos) ->
        let decls1 = 
          List.map (fun decl -> { decl with v_scope = scope }) decls
        in 
        LocalVars (decls1, pos)
    | Block (stmnts, pos) ->
        Block (List.map (fs pos) stmnts, pos)
    | If (cond, t, e, pos) ->
        If (cond, fs scope t, fs scope e, pos)
    | Loop (inv, preb, cond, postb, pos) ->
        Loop (inv, fs scope preb, cond, fs scope postb, pos)
    | stmnt -> stmnt
  in fs GrassUtil.global_scope stmnt

%}

%token <string> IDENT
%token <int> INTVAL
%token <bool> BOOLVAL
%token <string> STRINGVAL
%token LPAREN RPAREN LBRACE RBRACE 
%token COLON COLONEQ COLONCOLON SEMICOLON DOT PIPE
%token UMINUS PLUS MINUS DIV TIMES
%token UNION INTER DIFF
%token EQ NEQ LEQ GEQ LT GT IN NOTIN AT
%token PTS EMP NULL
%token SEPSTAR SEPPLUS SEPINCL AND OR IMPLIES IFF NOT COMMA
%token <SplSyntax.quantifier_kind> QUANT
%token ASSUME ASSERT CALL DISPOSE HAVOC NEW RETURN
%token IF ELSE WHILE
%token GHOST IMPLICIT VAR STRUCT PROCEDURE PREDICATE FUNCTION INCLUDE
%token OUTPUTS RETURNS REQUIRES ENSURES INVARIANT
%token INT BOOL SET
%token MATCHING YIELDS COMMENT 
%token EOF

%nonassoc COLONEQ 
%nonassoc ASSUME ASSERT
%nonassoc NEW DISPOSE

%left SEMICOLON
%left OR
%left AND
%right IMPLIES
%left SEP SEPINCL
%left DOT
%right NOT
%nonassoc IFF
%nonassoc LT GT LEQ GEQ
%nonassoc EQ NEQ 
%nonassoc PTS LS
%left PLUS MINUS
%left UNION INTER DIFF
%left TIMES DIV
%nonassoc LPAREN

%start main
%type <SplSyntax.spl_program> main
%%

main:
| declarations {
  extend_spl_program (fst $1) (snd $1) empty_spl_program
} 
;

declarations:
| include_cmd declarations 
  { (($1, mk_position 1 1) :: fst $2, snd $2) }
| proc_decl declarations 
  { (fst $2, ProcDecl $1 :: snd $2) }
|   pred_decl declarations 
  { (fst $2, PredDecl $1 :: snd $2) }
| struct_decl declarations
  { (fst $2, StructDecl $1 :: snd $2) }
| var_decl declarations
  { (fst $2, VarDecl $1 :: snd $2) }
| /* empty */ { ([], []) }
| error { ProgError.syntax_error (mk_position 1 1) None }
;

include_cmd:
| INCLUDE STRINGVAL SEMICOLON { $2 }

proc_decl:
| proc_header { proc_decl $1 (Skip GrassUtil.dummy_position) }
| proc_header proc_impl {
  proc_decl $1 $2
} 
;

proc_header:
| PROCEDURE IDENT LPAREN var_decls RPAREN proc_returns proc_contracts {  
  let formals, locals0 =
    List.fold_right (fun decl (formals, locals0) ->
      decl.v_name :: formals, IdMap.add decl.v_name decl locals0)
      $4 ([], IdMap.empty)
  in
  let returns, locals =
    List.fold_right (fun decl (returns, locals) ->
      decl.v_name :: returns, IdMap.add decl.v_name decl locals)
      $6 ([], locals0)
  in
  let decl = 
    { p_name = ($2, 0);
      p_formals = formals;  
      p_returns = returns; 
      p_locals = locals;
      p_contracts = $7;
      p_body = Skip GrassUtil.dummy_position; 
      p_pos = mk_position 2 2;
    }
  in 
  decl
} 
;

proc_contracts:
| proc_contract proc_contracts { $1 :: $2 }
| /* empty */ { [] }
;

proc_contract:
| REQUIRES expr semicolon_opt { Requires $2 }
| ENSURES expr semicolon_opt { Ensures $2 }
;

semicolon_opt:
| SEMICOLON {}
| /* empty */ {}
;

proc_impl:
| LBRACE block RBRACE { 
  fix_scopes (Block ($2, mk_position 1 3)) 
}
;

pred_decl:
| PREDICATE IDENT LPAREN var_decls RPAREN LBRACE expr RBRACE {
  let formals, locals =
    List.fold_right (fun decl (formals, locals) ->
      decl.v_name :: formals, IdMap.add decl.v_name decl locals)
      $4 ([], IdMap.empty)
  in
  let decl =
    { pr_name = ($2, 0);
      pr_formals = formals;
      pr_outputs = [];
      pr_locals = locals;
      pr_body = $7;
      pr_pos = mk_position 2 2;
    }
  in decl
}
| FUNCTION IDENT LPAREN var_decls RPAREN RETURNS LPAREN var_decls RPAREN LBRACE expr RBRACE {
  let formals, locals =
    List.fold_right (fun decl (formals, locals) ->
      decl.v_name :: formals, IdMap.add decl.v_name decl locals)
      $4 ([], IdMap.empty)
  in
  let outputs, locals =
    List.fold_right (fun decl (outputs, locals) ->
      decl.v_name :: outputs, IdMap.add decl.v_name decl locals)
      $8 ([], locals)
  in
  let decl =
    { pr_name = ($2, 0);
      pr_formals = formals;
      pr_outputs = outputs;
      pr_locals = locals;
      pr_body = $11;
      pr_pos = mk_position 2 2;
    }
  in decl
}
;

var_decls:
| var_decl var_decl_list { $1 :: $2 }
| /* empty */ { [] }
;

var_decl_list:
| COMMA var_decl var_decl_list { $2 :: $3 }
| /* empty */ { [] }
;

var_decl:
| var_modifier IDENT COLON var_type { 
  let decl = 
    { v_name = ($2, 0);
      v_type = $4;
      v_ghost = snd $1;
      v_implicit = fst $1;
      v_aux = false;
      v_pos = mk_position 2 2;
      v_scope = GrassUtil.global_scope; (* scope is fixed later *)
    } 
  in
  decl
}
;

var_modifier:
| IMPLICIT GHOST { true, true }
| GHOST { false, true }
| /* empty */ { false, false }
; 

var_type:
| INT { IntType }
| BOOL { BoolType }
| SET LT var_type GT { SetType $3 }
| IDENT { StructType ($1, 0) }
;

proc_returns:
| RETURNS LPAREN var_decls RPAREN { $3 }
| /* empty */ { [] }
;

struct_decl:
| STRUCT IDENT LBRACE field_decls RBRACE {
  let fields =
    List.fold_left (fun fields decl->
      IdMap.add decl.v_name decl fields)
      IdMap.empty $4
  in
  let decl = 
    { s_name = ($2, 0);
      s_fields = fields;
      s_pos = mk_position 2 2;
    } 
  in
  decl
}  
;

field_decls:
| field_decl field_decls { $1 :: $2 }
| /* empty */ { [] }
;

field_decl:
| VAR var_decl SEMICOLON { $2 }
;

block:
  stmt block { $1 :: $2 }
| /* empty */ { [] }
;

stmt:
| stmt_wo_trailing_substmt { $1 }
| if_then_stmt { $1 }
| if_then_else_stmt { $1 }
| while_stmt { $1 }
;

stmt_no_short_if:
| stmt_wo_trailing_substmt { $1 }
| if_then_else_stmt_no_short_if  { $1 }
| while_stmt_no_short_if  { $1 }
;

stmt_wo_trailing_substmt:
/* variable declaration */
| VAR var_decls SEMICOLON { LocalVars ($2, mk_position 1 3) }
/* nested block */
| LBRACE block RBRACE { 
  Block ($2, mk_position 1 3) 
}
/* deallocation */
| DISPOSE expr SEMICOLON { 
  Dispose ($2, mk_position 1 3)
}
/* procedure call */
| proc_call SEMICOLON {
  Assign ([], [$1], mk_position 1 1)
}
/* assignment */
| assign_lhs_list COLONEQ expr_list SEMICOLON {
  Assign ($1, $3, mk_position 1 4)
}
/* havoc */
| HAVOC expr_list_opt SEMICOLON { 
  Havoc ($2, mk_position 1 3)
}
/* assume */
| ASSUME expr SEMICOLON {
  Assume ($2, mk_position 1 3)
}
/* assert */
| ASSERT expr SEMICOLON { 
  Assert ($2, mk_position 1 3)
}
/* return */
| RETURN expr_list_opt SEMICOLON { 
  Return ($2, mk_position 1 3)
}
;

assign_lhs_list:
| assign_lhs COMMA assign_lhs_list { $1 :: $3 }
| assign_lhs { [$1] }
;

assign_lhs:
| ident { $1 }
| field_access { $1 }
;

if_then_stmt:
| IF LPAREN expr RPAREN stmt  { 
  If ($3, $5, Skip GrassUtil.dummy_position, mk_position 1 6)
}
;

if_then_else_stmt:
| IF LPAREN expr RPAREN stmt_no_short_if ELSE stmt { 
  If ($3, $5, $7, mk_position 1 7)
}
;

if_then_else_stmt_no_short_if:
| IF LPAREN expr RPAREN stmt_no_short_if ELSE stmt_no_short_if { 
  If ($3, $5, $7, mk_position 1 7)
}
;

while_stmt:
| WHILE LPAREN expr RPAREN loop_contracts LBRACE block RBRACE {
  Loop ($5, Skip GrassUtil.dummy_position, $3, Block ($7, mk_position 6 8), mk_position 1 8)
}
| WHILE LPAREN expr RPAREN stmt {
  Loop ([], Skip GrassUtil.dummy_position, $3, $5, mk_position 1 5)
}
;

while_stmt_no_short_if:
| WHILE LPAREN expr RPAREN stmt_no_short_if {
  Loop ([], Skip GrassUtil.dummy_position, $3, $5, mk_position 1 5)
} 
;

loop_contracts:
| loop_contract loop_contracts { $1 :: $2 }
| loop_contract { [$1] }
;

loop_contract:
| INVARIANT expr semicolon_opt { Invariant $2 }
;

primary:
| INTVAL { IntVal ($1, mk_position 1 1) }
| BOOLVAL { BoolVal ($1, mk_position 1 1) }
| NULL { Null (mk_position 1 1) }
| EMP { Emp (mk_position 1 1) }
| LPAREN expr RPAREN { $2 }
| alloc { $1 }
| proc_call { $1 }
;

alloc:
| NEW IDENT { New (($2, 0), mk_position 1 2) }
;

proc_call:
| SET LT var_type GT LPAREN RPAREN { Setenum ($3, [], mk_position 1 6) }
| SET LT var_type GT LPAREN expr_list RPAREN { Setenum ($3, $6, mk_position 1 6) }
| SET LPAREN expr_list RPAREN { Setenum (UniversalType, $3, mk_position 1 4) }
| IDENT LPAREN expr_list_opt RPAREN { ProcCall (($1, 0), $3, mk_position 1 4) }
;

ident: 
| IDENT { Ident (($1, 0), mk_position 1 1) }
;

field_access:
| unary_expr DOT IDENT { Dot ($1, ($3, 0), mk_position 1 3) }
;

unary_expr:
| primary { $1 }
| ident { $1 }
| field_access { $1 }
| PLUS unary_expr { UnaryOp (OpPlus, $2, mk_position 1 2) }
| MINUS unary_expr { UnaryOp (OpMinus, $2, mk_position 1 2) }
| unary_expr_not_plus_minus { $1 }
;

unary_expr_not_plus_minus:
| NOT unary_expr  { UnaryOp (OpNot, $2, mk_position 1 2) }
;

diff_expr:
| unary_expr { $1 }
| diff_expr DIFF unary_expr { BinaryOp ($1, OpDiff, $3, mk_position 1 3) }
;

mult_expr:
| diff_expr  { $1 }
| mult_expr TIMES diff_expr { BinaryOp ($1, OpMult, $3, mk_position 1 3) }
| mult_expr DIV diff_expr { BinaryOp ($1, OpDiv, $3, mk_position 1 3) }
| mult_expr INTER diff_expr { BinaryOp ($1, OpInt, $3, mk_position 1 3) }
;

add_expr:
| mult_expr { $1 }
| add_expr PLUS mult_expr { BinaryOp ($1, OpPlus, $3, mk_position 1 3) }
| add_expr MINUS mult_expr { BinaryOp ($1, OpMinus, $3, mk_position 1 3) }
| add_expr UNION mult_expr { BinaryOp ($1, OpUn, $3, mk_position 1 3) }
;

pts_expr:
| add_expr { $1 }
| pts_expr PTS add_expr { BinaryOp ($1, OpPts, $3, mk_position 1 3) }
;

rel_expr:
| pts_expr { $1 }
| rel_expr LT pts_expr { BinaryOp ($1, OpLt, $3, mk_position 1 3) }
| rel_expr GT pts_expr { BinaryOp ($1, OpGt, $3, mk_position 1 3) }
| rel_expr LEQ pts_expr { BinaryOp ($1, OpLeq, $3, mk_position 1 3) }
| rel_expr GEQ pts_expr { BinaryOp ($1, OpGeq, $3, mk_position 1 3) }
| rel_expr IN pts_expr { BinaryOp ($1, OpIn, $3, mk_position 1 3) }
| rel_expr NOTIN pts_expr { UnaryOp (OpNot, BinaryOp ($1, OpIn, $3, mk_position 1 3), mk_position 1 3) }
;

eq_expr:
| rel_expr { $1 }
| eq_expr EQ eq_expr { BinaryOp ($1, OpEq, $3, mk_position 1 3) }
| eq_expr NEQ eq_expr { BinaryOp ($1, OpNeq, $3, mk_position 1 3) }
;

sep_star_expr:
| eq_expr { $1 }
| sep_star_expr SEPSTAR eq_expr { BinaryOp ($1, OpSepStar, $3, mk_position 1 3) }
;

sep_plus_expr:
| sep_star_expr { $1 }
| sep_plus_expr SEPPLUS sep_star_expr { BinaryOp ($1, OpSepPlus, $3, mk_position 1 3) }
;

sep_incl_expr:
| sep_plus_expr { $1 }
| sep_incl_expr SEPINCL sep_plus_expr { BinaryOp ($1, OpSepIncl, $3, mk_position 1 3) }
;

and_expr:
| sep_incl_expr { $1 }
| and_expr AND sep_incl_expr { BinaryOp ($1, OpAnd, $3, mk_position 1 3) }
;

or_expr:
| and_expr { $1 }
| or_expr OR and_expr { BinaryOp ($1, OpOr, $3, mk_position 1 3) }
;

impl_expr:
| or_expr { $1 }
| or_expr IMPLIES impl_expr { BinaryOp ($1, OpImpl, $3, mk_position 1 3) }
;

iff_expr:
| impl_expr { $1 }
| iff_expr IFF iff_expr { BinaryOp ($1, OpEq, $3, mk_position 1 3) }
;

annot_expr:
| iff_expr { $1 }
| annot_expr AT LPAREN annot RPAREN { Annot ($1, $4, mk_position 1 5) }

quant_expr: 
| annot_expr { $1 }
| QUANT IDENT IN quant_expr COLONCOLON annot_expr { GuardedQuant ($1, ($2, 0), $4, $6, mk_position 1 6) }
| QUANT IDENT COLON var_type var_decl_list COLONCOLON annot_expr { 
  let decl = 
    { v_name = ($2, 0);
      v_type = $4;
      v_ghost = false;
      v_implicit = false;
      v_aux = false;
      v_pos = mk_position 2 2;
      v_scope = mk_position 1 7
    } 
  in
  Quant ($1, decl :: $5, $7, mk_position 1 7) 
}
;

expr:
| quant_expr { $1 } 
;

expr_list_opt:
| expr_list { $1 }
| /* empty */ { [] }
;

expr_list:
| expr COMMA expr_list { $1 :: $3 }
| expr { [$1] }
;

annot:
| MATCHING expr_list YIELDS expr { GeneratorAnnot($2, $4) }
| COMMENT STRINGVAL { CommentAnnot ($2) }

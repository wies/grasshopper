%{
open Util
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
    | LocalVars (decls, es_opt, pos) ->
        let decls1 = 
          List.map (fun decl -> { decl with v_scope = scope }) decls
        in 
        LocalVars (decls1, es_opt, pos)
    | Block (stmnts, pos) ->
        Block (List.map (fs pos) stmnts, pos)
    | If (cond, t, e, pos) ->
        If (cond, fs scope t, fs scope e, pos)
    | Choice (stmnts, pos) ->
        Choice (List.map (fs scope) stmnts, pos)
    | Loop (inv, preb, cond, postb, pos) ->
        Loop (inv, fs scope preb, cond, fs scope postb, pos)
    | stmnt -> stmnt
  in fs GrassUtil.global_scope stmnt

let fst3 (v, _, _) = v
let snd3 (_, v, _) = v
let trd3 (_, _, v) = v


type rhs_string_maybe =
  | StringRHS of string
  | NormalRHS of exprs

%}

%token <string * int> IDENT
%token <Int64.t> INTVAL
%token <char> CHARVAL
%token <bool> BOOLVAL
%token <string> STRINGVAL
%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET
%token COR, CHOOSE COLON COLONEQ COLONCOLON SEMICOLON DOT PIPE
%token UMINUS PLUS MINUS DIV TIMES MOD
%token UNION INTER DIFF
%token EQ NEQ LEQ GEQ LT GT IN NOTIN AT
%token AMP TILDE BSL BSR INT2BYTE BYTE2INT
%token PTS EMP NULL
%token SEPSTAR SEPPLUS SEPINCL AND OR IMPLIES IFF NOT COMMA
%token <SplSyntax.binder_kind> QUANT
%token ASSUME ASSERT SPLIT CALL FREE HAVOC NEW RETURN
%token IF ELSE WHILE
%token GHOST IMPLICIT VAR STRUCT PURE LEMMA PROCEDURE PREDICATE FUNCTION INCLUDE AXIOM TYPE
%token DEFINE DATATYPE OUTPUTS RETURNS REQUIRES ENSURES INVARIANT
%token LOC INT BOOL BYTE SET MAP ARRAY ARRAYCELL
%token MATCHING YIELDS WITHOUT COMMENT PATTERN
%token EOF

%nonassoc COLONEQ 
%nonassoc ASSUME ASSERT SPLIT
%nonassoc NEW FREE

%nonassoc LOWER_THAN_COR
%nonassoc COR  

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
%left TIMES DIV MOD
%nonassoc LPAREN

%start main
%type <SplSyntax.spl_program> main
%%

main:
| declarations {
  extend_spl_program (fst3 $1) (snd3 $1) (trd3 $1) empty_spl_program
} 
;

declarations:
| background_th declarations
  { (fst3 $2, snd3 $2, ($1, mk_position 1 1) :: trd3 $2) }
| include_cmd declarations 
  { (($1, mk_position 1 1) :: fst3 $2, snd3 $2, trd3 $2) }
| type_decl declarations
  { (fst3 $2, TypeDecl $1 :: snd3 $2, trd3 $2) }
| proc_decl declarations 
  { (fst3 $2, ProcDecl $1 :: snd3 $2, trd3 $2) }
| pred_decl declarations 
  { (fst3 $2, PredDecl $1 :: snd3 $2, trd3 $2) }
| macro_decl declarations
  { (fst3 $2, MacroDecl $1 :: snd3 $2, trd3 $2) }
| VAR var_decl SEMICOLON declarations
  { (fst3 $4, VarDecl $2 :: snd3 $4, trd3 $4) }
| /* empty */ { ([], [], []) }
| error { ProgError.syntax_error (mk_position 1 1) None }
;

include_cmd:
| INCLUDE STRINGVAL semicolon_opt { $2 }
;
  
background_th:
| AXIOM expr semicolon_opt { $2 }
;
  
type_decl:
| TYPE IDENT semicolon_opt {
  { t_name = $2;
    t_def = FreeTypeDef;
    t_pos = mk_position 2 2 }
}
| datatype_decl { $1 }
| struct_decl { $1 }
;

ident_list_opt:
| ident_list { $1 }
| /* empty */ { [] }
;

ident_list:
| IDENT COMMA ident_list { $1 :: $3 }
| IDENT { [$1] }
;

macro_decl:
| DEFINE IDENT LPAREN ident_list_opt RPAREN LBRACE expr RBRACE {
  { m_name = $2;
    m_args = $4;
    m_body = $7;
    m_pos = mk_position 1 8;
  }
}
;

proc_decl:
| proc_header { $1 }
| proc_header proc_impl {
  proc_decl $1 $2
} 
;

proc_header:
| proc_head {
  let name, formals0, returns0, contracts, pos, is_lemma = $1 in
  let formals, locals0 =
    List.fold_right (fun decl (formals, locals0) ->
      decl.v_name :: formals, IdMap.add decl.v_name decl locals0)
      formals0 ([], IdMap.empty)
  in
  let returns, locals =
    List.fold_right (fun decl (returns, locals) ->
      decl.v_name :: returns, IdMap.add decl.v_name decl locals)
      returns0 ([], locals0)
  in
  let decl = 
    { p_name = name;
      p_formals = formals;  
      p_returns = returns; 
      p_locals = locals;
      p_contracts = contracts;
      p_is_lemma = is_lemma;
      p_body = Skip GrassUtil.dummy_position;
      p_pos = pos;
    }
  in 
  decl
}
;

proc_head:
| PROCEDURE IDENT LPAREN var_decls RPAREN proc_returns contracts {
  ($2, $4, $6, $7, mk_position 2 2, false)
}
| LEMMA IDENT LPAREN var_decls RPAREN proc_returns contracts {
  ($2, $4, $6, $7, mk_position 2 2, true)
}
;
  
contracts:
| contract contracts { $1 :: $2 }
| /* empty */ { [] }
;

contract:
| contract_mods REQUIRES expr semicolon_opt { Requires ($3, fst $1, snd $1) }
| contract_mods ENSURES expr semicolon_opt { Ensures ($3, fst $1, snd $1) }
;

contract_mods:
| PURE contract_mods { (true, snd $2) }
| FREE contract_mods { (fst $2, true) }
| /* empty */ { (false, false) }
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
| PREDICATE IDENT LPAREN var_decls RPAREN contracts pred_impl {
  let formals, locals =
    List.fold_right (fun decl (formals, locals) ->
      decl.v_name :: formals, IdMap.add decl.v_name decl locals)
      $4 ([], IdMap.empty)
  in
  let decl =
    { pr_name = $2;
      pr_formals = formals;
      pr_outputs = [];
      pr_locals = locals;
      pr_contracts = $6;
      pr_body = $7;
      pr_pos = mk_position 2 2;
    }
  in decl
}
| function_header pred_impl {
  pred_decl $1 $2
}
;

function_header:
| FUNCTION IDENT LPAREN var_decls RPAREN RETURNS LPAREN var_decls RPAREN contracts {
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
  let contracts =
    List.map (function Ensures (e, _, free) -> Ensures (e, true, free) | c -> c) $10
  in
  let decl =
    { pr_name = $2;
      pr_formals = formals;
      pr_outputs = outputs;
      pr_locals = locals;
      pr_contracts = contracts;
      pr_body = None;
      pr_pos = mk_position 2 2;
    }
  in decl
}
;
  
pred_impl:
| LBRACE expr RBRACE {
  Some $2
}
| /* empty */ { None }
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
    { v_name = $2;
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

var_decls_opt_type:
| var_decl var_decl_opt_type_list { $1 :: $2 }
| var_decl_opt_type var_decl_opt_type_list { $1 :: $2 }
| /* empty */ { [] }
;

var_decl_opt_type_list:
| COMMA var_decl var_decl_opt_type_list { $2 :: $3 }
| COMMA var_decl_opt_type var_decl_opt_type_list { $2 :: $3 }
| /* empty */ { [] }
;

var_decl_opt_type:
| var_modifier IDENT { 
  let decl = 
    { v_name = $2;
      v_type = AnyType;
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
| LOC LT IDENT GT { StructType $3 }
| INT { IntType }
| BOOL { BoolType }
| BYTE { ByteType }
| ARRAY LT var_type GT { ArrayType $3 }
| ARRAYCELL LT var_type GT { ArrayCellType $3 }
| SET LT var_type GT { SetType $3 }
| MAP LT var_type COMMA var_type GT { MapType ($3, $5) }
| IDENT { IdentType $1 }
;

proc_returns:
| RETURNS LPAREN var_decls RPAREN { $3 }
| /* empty */ { [] }
;

datatype_decl:
| DATATYPE IDENT EQ constr_decls SEMICOLON {
  { t_name = $2;
    t_def = ADTypeDef $4;
    t_pos = mk_position 1 5;
  }
};

constr_decls:
| constr_decl { [$1] }
| constr_decl PIPE constr_decls { $1 :: $3 }
;
  
constr_decl:
| IDENT { { c_name = $1; c_args = []; c_pos = mk_position 1 1 } }
| IDENT LPAREN constr_args RPAREN { { c_name = $1; c_args = $3; c_pos = mk_position 1 1 } }
;

constr_args:
| constr_arg { [$1] }
| constr_arg COMMA constr_args { $1 :: $3 }
;

constr_arg:
| IDENT COLON var_type { var_decl $1 $3 false false (mk_position 1 3) GrassUtil.global_scope } 
;
  
struct_decl:
| STRUCT IDENT LBRACE field_decls RBRACE {
  let fields =
    List.fold_left (fun fields decl->
      IdMap.add decl.v_name decl fields)
      IdMap.empty $4
  in
  let decl = 
    { t_name = $2;
      t_def = StructTypeDef fields;
      t_pos = mk_position 2 2;
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
| choice_stmt { $1 }
;

stmt_no_short_if:
| stmt_wo_trailing_substmt { $1 }
| if_then_else_stmt_no_short_if  { $1 }
| while_stmt_no_short_if  { $1 }
| choice_stmt_no_short_if { $1 }
;

stmt_wo_trailing_substmt:
/* variable declaration */
| VAR var_decls SEMICOLON { LocalVars ($2, None, mk_position 1 3) }
| VAR var_decls_opt_type COLONEQ expr_list SEMICOLON { LocalVars ($2, Some $4, mk_position 1 5) }
/* nested block */
| LBRACE block RBRACE { 
  Block ($2, mk_position 1 3) 
}
/* deallocation */
| FREE expr SEMICOLON { 
  Dispose ($2, mk_position 1 3)
}
/* procedure call */
| proc_call SEMICOLON {
  Assign ([], [$1], mk_position 1 1)
}
/* assignment */
| assign_lhs_list COLONEQ expr_list_string SEMICOLON {
  let lhs = $1 in
  match $3 with
  | NormalRHS es -> Assign (lhs, es, mk_position 1 4)
  | StringRHS str ->
    assert (List.length lhs = 1);
    let lhs = List.hd lhs in
    let pos1 = mk_position 1 4 in
    let pos2 = mk_position 3 3 in
    let pos3 = mk_position 1 1 in
    let char_to_byte c =
      UnaryOp (OpToByte, IntVal(Int64.of_int (int_of_char c), pos2), pos2)
    in
    let mk_assign idx value =
      let lhs_read = Read (lhs, IntVal(Int64.of_int idx, pos3), pos3) in
      Assign([lhs_read], [value], pos1)
    in
    let rec to_list n = 
      if n >= (String.length str) then 
        let v = UnaryOp (OpToByte, IntVal(Int64.zero, pos2), pos2) in
        [mk_assign n v]
      else
        let v = char_to_byte (String.get str n) in
        let a = mk_assign n v in
        a :: (to_list (n+1))
    in
    Block (to_list 0, pos1)
}
/* havoc */
| HAVOC expr_list_opt SEMICOLON { 
  Havoc ($2, mk_position 1 3)
}
/* assume */
| contract_mods ASSUME expr SEMICOLON {
  Assume ($3, fst $1, mk_position (if $1 <> (false, false) then 1 else 2) 4)
}
/* assert */
| contract_mods ASSERT expr SEMICOLON { 
  Assert ($3, fst $1, mk_position (if $1 <> (false, false) then 1 else 2) 4)
}
/* split */
| SPLIT expr SEMICOLON { 
  Split ($2, mk_position 1 3)
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
| field_access_no_set { $1 }
| array_access_no_set { $1 }
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

choice_stmt:
| CHOOSE or_stmts {
  Choice ($2, mk_position 1 2)
}
;

or_stmts:
| stmt COR or_stmts { $1 :: $3 }
| stmt { [$1] } %prec LOWER_THAN_COR
;

choice_stmt_no_short_if:
| CHOOSE or_stmts_no_short_if {
  Choice ($2, mk_position 1 2)
}
;

or_stmts_no_short_if:
| stmt COR or_stmts_no_short_if { $1 :: $3 }
| stmt_no_short_if { [$1] }
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
| contract_mods INVARIANT expr semicolon_opt { Invariant ($3, fst $1) }
;

primary:
| INTVAL { IntVal ($1, mk_position 1 1) }
| BOOLVAL { BoolVal ($1, mk_position 1 1) }
| CHARVAL { UnaryOp (OpToByte, IntVal(Int64.of_int (int_of_char $1), mk_position 1 1), mk_position 1 1) }
/* TODO Byte literal */
| NULL { Null (AnyRefType, mk_position 1 1) }
| EMP { Emp (mk_position 1 1) }
| LPAREN expr RPAREN { $2 }
| set_expr { $1 }
| alloc { $1 }
| proc_call { $1 }
| field_access { $1 }
| field_write { $1 }
| array_access { $1 }
| cast { $1 }
    ;

primary_no_set:
| INTVAL { IntVal ($1, mk_position 1 1) }
| BOOLVAL { BoolVal ($1, mk_position 1 1) }
| CHARVAL { UnaryOp (OpToByte, IntVal(Int64.of_int (int_of_char $1), mk_position 1 1), mk_position 1 1) }
/* TODO Byte literal */
| NULL { Null (AnyRefType, mk_position 1 1) }
| EMP { Emp (mk_position 1 1) }
| LPAREN expr RPAREN { $2 }
| alloc { $1 }
| proc_call { $1 }
| field_access_no_set { $1 }
| array_access_no_set { $1 }
| cast { $1 }
;

set_expr:
| LBRACE expr_list_opt RBRACE { Setenum (AnyType, $2, mk_position 1 3) }
| LBRACE simple_bound_var COLONCOLON expr RBRACE { Binder (SetComp, [$2], $4, mk_position 1 5) }
;
  
alloc:
| NEW var_type { New ($2, [], mk_position 1 2) }
| NEW var_type LPAREN expr_list_opt RPAREN { New ($2, $4, mk_position 1 5) }
;

proc_call:
| SET LT var_type GT LPAREN expr_list_opt RPAREN { Setenum ($3, $6, mk_position 1 6) }
| SET LPAREN expr_list_opt RPAREN { Setenum (AnyType, $3, mk_position 1 4) }
/*| MAP LT var_type, var_type GT LPAREN expr_list_opt RPAREN {*/
| IDENT LPAREN expr_list_opt RPAREN { ProcCall ($1, $3, mk_position 1 4) }
;
                                                             
ident: 
| IDENT { Ident ($1, mk_position 1 1) }
;

field_access:
| ident DOT ident { Read ($3, $1, mk_position 1 3) }
| primary DOT ident { Read ($3, $1, mk_position 1 3) }
;

field_access_no_set:
| ident DOT ident { Read ($3, $1, mk_position 1 3) }
| primary_no_set DOT ident { Read ($3, $1, mk_position 1 3) }
;

field_write:
| ident LBRACKET expr COLONEQ expr RBRACKET {
  Write ($1, $3, $5, mk_position 1 6)
}
;
  
array_access:
| ident LBRACKET expr RBRACKET { Read ($1, $3, mk_position 1 4) }
| primary LBRACKET expr RBRACKET { Read ($1, $3, mk_position 1 4) }
| ident LBRACKET RBRACKET { Read (Read (Ident (("array", 0), mk_position 2 3), $1, mk_position 1 3),
                                  Read (Ident (("index", 0), mk_position 2 3), $1, mk_position 1 3), mk_position 1 3) }
| primary LBRACKET RBRACKET { Read (Read (Ident (("array", 0), mk_position 2 3), $1, mk_position 1 3),
                                    Read (Ident (("index", 0), mk_position 2 3), $1, mk_position 1 3), mk_position 1 3) }
;

array_access_no_set:
| ident LBRACKET expr RBRACKET { Read ($1, $3, mk_position 1 4) }
| primary_no_set LBRACKET expr RBRACKET { Read ($1, $3, mk_position 1 4) }
| ident LBRACKET RBRACKET { Read (Read (Ident (("array", 0), mk_position 2 3), $1, mk_position 1 3),
                                  Read (Ident (("index", 0), mk_position 2 3), $1, mk_position 1 3), mk_position 1 3) }
| primary_no_set LBRACKET RBRACKET { Read (Read (Ident (("array", 0), mk_position 2 3), $1, mk_position 1 3),
                                           Read (Ident (("index", 0), mk_position 2 3), $1, mk_position 1 3), mk_position 1 3) }
;

cast:
| INT2BYTE LPAREN expr RPAREN { UnaryOp (OpToByte, $3, mk_position 1 4) }
| BYTE2INT LPAREN expr RPAREN { UnaryOp (OpToInt, $3, mk_position 1 4) }
;
                                                              
unary_expr:
| primary { $1 }
| ident { $1 }
| PLUS unary_expr { UnaryOp (OpUPlus, $2, mk_position 1 2) }
| MINUS unary_expr { UnaryOp (OpUMinus, $2, mk_position 1 2) }
| unary_expr_not_plus_minus { $1 }
;

unary_expr_not_plus_minus:
| NOT unary_expr  { UnaryOp (OpNot, $2, mk_position 1 2) }
| TILDE unary_expr  { UnaryOp (OpBvNot, $2, mk_position 1 2) }
;

diff_expr:
| unary_expr { $1 }
| diff_expr DIFF unary_expr { BinaryOp ($1, OpDiff, $3, SetType AnyType, mk_position 1 3) }
| diff_expr BSL  unary_expr { BinaryOp ($1, OpBvShiftL, $3, IntType, mk_position 1 3) }
| diff_expr BSR  unary_expr { BinaryOp ($1, OpBvShiftR, $3, IntType, mk_position 1 3) }
;

mult_expr:
| diff_expr  { $1 }
| mult_expr TIMES diff_expr { BinaryOp ($1, OpMult, $3, IntType, mk_position 1 3) }
| mult_expr DIV diff_expr { BinaryOp ($1, OpDiv, $3, IntType, mk_position 1 3) }
| mult_expr MOD diff_expr { BinaryOp ($1, OpMod, $3, IntType, mk_position 1 3) }
| mult_expr INTER diff_expr { BinaryOp ($1, OpInt, $3, SetType AnyType, mk_position 1 3) }
| mult_expr AMP diff_expr { BinaryOp ($1, OpBvAnd, $3, IntType, mk_position 1 3) }
;

add_expr:
| mult_expr { $1 }
| add_expr PLUS mult_expr { BinaryOp ($1, OpPlus, $3, IntType, mk_position 1 3) }
| add_expr MINUS mult_expr { BinaryOp ($1, OpMinus, $3, IntType, mk_position 1 3) }
| add_expr UNION mult_expr { BinaryOp ($1, OpUn, $3, SetType AnyType, mk_position 1 3) }
| add_expr PIPE mult_expr { BinaryOp ($1, OpBvOr, $3, IntType, mk_position 1 3) }
;

pts_expr:
| add_expr { $1 }
| pts_expr PTS add_expr { BinaryOp ($1, OpPts, $3, PermType, mk_position 1 3) }
;
  
rel_expr:
| comp_seq {
  match $1 with
  | e, [] -> e
  | _, comps ->
      List.fold_right
        (fun l r_opt ->
          r_opt |>
          Opt.map
            (fun r -> BinaryOp (l, OpAnd, r, BoolType, GrassUtil.merge_src_pos (pos_of_expr l) (pos_of_expr r))) |>
            Opt.some l)
        comps None |>
        Opt.get
}
| rel_expr IN pts_expr { BinaryOp ($1, OpIn, $3, BoolType, mk_position 1 3) }
| rel_expr NOTIN pts_expr { UnaryOp (OpNot, BinaryOp ($1, OpIn, $3, BoolType, mk_position 1 3), mk_position 1 3) }
;

comp_op:
| LT { OpLt }
| GT { OpGt }
| LEQ { OpLeq }
| GEQ { OpGeq }
;

comp_seq:
| pts_expr { ($1, []) }
| pts_expr comp_op comp_seq {
  let arg2, comps = $3 in
  let arg1_pos = mk_position 1 1 in
  ($1, BinaryOp ($1, $2, arg2, BoolType, GrassUtil.merge_src_pos arg1_pos (pos_of_expr arg2)) :: comps)
}
;
  
eq_expr:
| rel_expr { $1 }
| eq_expr EQ eq_expr { BinaryOp ($1, OpEq, $3, BoolType, mk_position 1 3) }
| eq_expr NEQ eq_expr { UnaryOp (OpNot, BinaryOp ($1, OpEq, $3, BoolType, mk_position 1 3), mk_position 1 3) }
;

dirty_expr:
| eq_expr { $1 }
| LBRACKET expr RBRACKET LPAREN expr_list RPAREN { Dirty ($2, $5, mk_position 1 6) }

and_expr:
| dirty_expr { $1 }
| and_expr AND dirty_expr { BinaryOp ($1, OpAnd, $3, AnyType, mk_position 1 3) }
;

sep_star_expr:
| and_expr { $1 }
| sep_star_expr SEPSTAR and_expr { BinaryOp ($1, OpSepStar, $3, PermType, mk_position 1 3) }
;

sep_plus_expr:
| sep_star_expr { $1 }
| sep_plus_expr SEPPLUS sep_star_expr { BinaryOp ($1, OpSepPlus, $3, PermType, mk_position 1 3) }
;

sep_incl_expr:
| sep_plus_expr { $1 }
| sep_incl_expr SEPINCL sep_plus_expr { BinaryOp ($1, OpSepIncl, $3, PermType, mk_position 1 3) }
;

or_expr:
| sep_incl_expr { $1 }
| or_expr OR sep_incl_expr { BinaryOp ($1, OpOr, $3, AnyType, mk_position 1 3) }
;

impl_expr:
| or_expr { $1 }
| or_expr IMPLIES impl_expr { BinaryOp ($1, OpImpl, $3, BoolType, mk_position 1 3) }
;

iff_expr:
| impl_expr { $1 }
| iff_expr IFF iff_expr { BinaryOp ($1, OpEq, $3, BoolType, mk_position 1 3) }
;

annot_expr:
| iff_expr { $1 }
| annot_expr AT LPAREN annot RPAREN { Annot ($1, $4, mk_position 1 5) }


quant_var:
| IDENT IN annot_expr {
    GuardedVar ($1, $3)
  }
| simple_bound_var { $1 }
;
  
simple_bound_var:      
| IDENT COLON var_type {
    let decl = { v_name = $1;
                 v_type = $3;
                 v_ghost = false;
                 v_implicit = false;
                 v_aux = false;
                 v_pos = mk_position 1 3;
                 v_scope = GrassUtil.global_scope; (* scope is fixed later *) } in
    UnguardedVar decl
  }
;

quant_var_list:
| COMMA quant_var quant_var_list { $2 :: $3 }
| /* empty */ { [] }
;

quant_vars:
| quant_var quant_var_list { $1 :: $2 }
;

quant_expr: 
| annot_expr { $1 }
| QUANT quant_vars COLONCOLON quant_expr { Binder ($1, $2, $4, mk_position 1 4) }
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

expr_list_string:
| STRINGVAL { StringRHS $1 }
| expr_list { NormalRHS $1 }
;

annot:
| MATCHING ematch_list YIELDS expr { GeneratorAnnot($2, $4) }
| PATTERN expr { PatternAnnot $2 }
| COMMENT STRINGVAL { CommentAnnot ($2) }

ematch_list:
| ematch { [$1] }
| ematch COMMA ematch_list { $1 :: $3 }

ematch:
| expr { ($1, []) }
| expr WITHOUT IDENT { ($1, [$3]) }

%{
  open Grass
  open SplSyntax
  open Lexing

  let pos = GrassUtil.dummy_position

  let mk_position s e =
    let start_pos = Parsing.rhs_start_pos s in
    let end_pos = Parsing.rhs_end_pos e in
    { sp_file = "predictor_output";
      sp_start_line = start_pos.pos_lnum;
      sp_start_col = start_pos.pos_cnum - start_pos.pos_bol;
      sp_end_line = end_pos.pos_lnum;
      sp_end_col = end_pos.pos_cnum - end_pos.pos_bol;
    }

%}

%token <string> ID
%token EXBINDING TRUE EMP NIL
%token LSEG
%token PREDICTION PRED_PROB
%token LAND NE EQ
%token STAR RIGHTARROW BACKSLASH NONE PIPE
%token COLON COMMA PERIOD
%token LPAREN RPAREN LBRACK RBRACK LCURLY RCURLY
%token EOF EOL

%start formulae

%type <SplSyntax.expr list> formulae

%%

formulae :
    | formula EOL  { [$1] }
    | formula EOL formulae  { $1 :: $3 }

formula :
/*    | EXBINDING varList PERIOD pureFormula COLON spatialFormula
        { SymHeap.ofSeqs $2 $6 $8 (fst $10) (snd $10) } */
    | pred_accuracy COLON pureFormula COLON spatialFormula
        { BinaryOp ($3, OpSepStar, $5, PermType, mk_position 3 5) }
    ;

pred_accuracy :
    | PREDICTION LCURLY PRED_PROB RCURLY { () }

var : ID { let decl =
	     { v_name = ($1, 0);
	       v_type = StructType ("Node", 0);
	       v_ghost = false;
	       v_implicit = false;
	       v_aux = false;
	       v_pos = mk_position 1 1;
	       v_scope = GrassUtil.global_scope; (* TODO scope is fixed later?? *)
	     }
	   in
	   decl
	 }
    ;

varList :
    | var               { [ $1 ] }
    | var COMMA varList { $1 :: $3 }
    ;

expr :
    | NIL  { Null (AnyRefType, mk_position 1 1) }
    | ID  { Ident (($1, 0), mk_position 1 1) }
    ;

exprList :
    | expr                { [ $1 ] }
    | expr COMMA exprList { $1 :: $3 }
    ;

pureFormulaAtom :
    | expr NE expr { UnaryOp (OpNot, BinaryOp ($1, OpEq, $3, BoolType, mk_position 1 3), mk_position 1 3) }
    | expr EQ expr { BinaryOp ($1, OpEq, $3, BoolType, mk_position 1 3) }
    ;

pureFormula :
    | pureFormulaAtom LAND pureFormula { BinaryOp ($1, OpAnd, $3, AnyType, mk_position 1 3)}
    | pureFormulaAtom                  { $1 }
    | TRUE                             { BoolVal (true, mk_position 1 1) }
    ;
/*
pointsTo :
    | expr RIGHTARROW LBRACK exprList RBRACK
        { PointsTo ($1, $4) }
*/
predicate :
/*    | ID LPAREN exprList PIPE BACKSLASH formula RPAREN
        { Predicate (PredicateName.FromString $1, Some $6, $3) } */
    | LSEG LPAREN exprList PIPE NONE RPAREN
        { ProcCall (("lseg", 0), $3, mk_position 1 4) }
    | ID LPAREN exprList PIPE NONE RPAREN
        { ProcCall (($1, 0), $3, mk_position 1 4) }
    ;

spatialFormula :
    | TRUE                                   { BoolVal (true, mk_position 1 1) }
    | predicate STAR spatialFormula          { BinaryOp ($1, OpSepStar, $3, PermType, mk_position 1 3) }
    | predicate                              { $1 }
    | EMP                                    { Emp (mk_position 1 1) }
      /*
    | pointsTo STAR spatialFormula           { (fst $3, $1 :: snd $3) }
    | pointsTo                               { ([], [$1]) } */
    ;

%{
open Form
open FormUtil
open Grass

let parse_error = ParseError.parse_error

%}

%token SET_LOGIC, SET_OPTION
%token DECLARE_SORT, DECLARE_FUN
%token BOOL_SORT, LOC_SORT, FLD_SORT, SET_SORT
%token <Form.binder> BINDER
%token <Form.boolOp> BOOLOP
%token <bool> BOOL_VAL
%token <int> INT_VAL
%token ASSERT, CHECK_SAT, GET_MODEL, EXIT
%token NAMED, BANG, LPAREN, RPAREN
%token <Form.symbol> SYMBOL
%token <Form.ident> IDENT
%token EOF

%start main
%type <Grass.command> main
%%

main:
  LPAREN cmnd RPAREN { $2 }
| EOF { Exit }
;

cmnd:
| SET_LOGIC IDENT { Skip }
| SET_OPTION IDENT BOOL_VAL { Skip }
| DECLARE_SORT sortid INT_VAL { Skip }
| DECLARE_FUN funid LPAREN sorts RPAREN sort { 
  decl_symbol $2 ($4, $6);
  Skip 
}
| ASSERT form { Assert $2 }
| CHECK_SAT { CheckSat }
| GET_MODEL { GetModel }
| EXIT { Exit }

sortid:
| LOC_SORT { }
| FLD_SORT { }
| SET_SORT { }
| IDENT { }

funid:
| SYMBOL { $1 }
| IDENT { FreeSym $1 }

sorts:
| sort sorts { $1 :: $2 }
| /* empty */ { [] }

sort: 
| BOOL_SORT { Bool }
| LOC_SORT { Loc }
| LPAREN FLD_SORT sort RPAREN { Fld $3 } 
| LPAREN SET_SORT sort RPAREN { Set $3 }

forms:
| form forms { $1 :: $2 }
| /* empty */ { [] }

form:
| BOOL_VAL { if $1 then mk_true else mk_false }
| LPAREN BOOLOP forms RPAREN { smk_op $2 $3 }
| LPAREN BINDER LPAREN vars RPAREN form RPAREN {
  List.iter (fun (id, _) -> remove_bound_var id) $4; 
  mk_binder $2 $4 $6
}
| LPAREN BANG form NAMED IDENT RPAREN {
  mk_comment (fst $5) $3
} 
| LPAREN IDENT terms RPAREN { 
  (* TODO: type check *)
  mk_pred $2 $3
} 
| LPAREN SYMBOL terms RPAREN { 
  (* TODO: type check *)
  match $2 with
  | Eq -> 
      (match $3 with 
      | [s; t] -> mk_eq s t
      | _ -> failwith ("Parse error: expected two arguments for " ^ (str_of_symbol $2)))
  | Elem -> 
      (match $3 with 
      | [s; t] -> mk_elem s t
      | _ -> failwith ("Parse error: expected two arguments for " ^ (str_of_symbol $2)))
  | SubsetEq ->
      (match $3 with 
      | [s; t] -> mk_subseteq s t
      | _ -> failwith ("Parse error: expected two arguments for " ^ (str_of_symbol $2)))
  | Btwn ->
      (match $3 with 
      | [f; s; t; u] -> mk_btwn f s t u
      | _ -> failwith ("Parse error: expected 4 arguments for " ^ (str_of_symbol $2)))
  | Frame ->
      (match $3 with 
      | x :: a :: lst -> mk_frame_lst x a lst
      | _ -> failwith ("Parse error: expected at least 2 arguments for " ^ (str_of_symbol $2)))
  | sym -> failwith ("Expected predicate symbol but found " ^ (str_of_symbol sym))
} 

vars:
| var vars { $1 :: $2 }
| /* empty */ { [] }

var:
| LPAREN IDENT sort RPAREN { decl_bound_var $2 $3; ($2, $3) }


terms:
| term terms { $1 :: $2 }
| /* empty */ { [] }

term:
| SYMBOL {
  match $1 with
  | Null -> mk_null
  | Empty -> mk_empty None
  | sym -> failwith ("Expected constant symbol but found " ^ (str_of_symbol sym))
} 
| IDENT { 
  resolve_id_to_term $1
} 
| LPAREN SYMBOL terms RPAREN {
  (* TODO: check types *)
  match $2 with
  | Read ->
      (match $3 with 
      | [f; s] -> mk_read f s
      | _ -> failwith ("Parse error: expected 2 arguments for " ^ (str_of_symbol $2)))
  | Write ->
      (match $3 with 
      | [f; s; t] -> mk_write f s t
      | _ -> failwith ("Parse error: expected 3 arguments for " ^ (str_of_symbol $2)))
  | EntPnt ->
      (match $3 with 
      | [f; s; t] -> mk_ep f s t
      | _ -> failwith ("Parse error: expected 3 arguments for " ^ (str_of_symbol $2)))
  | SetEnum -> mk_setenum $3
  | Union -> mk_union $3
  | Inter -> mk_inter $3
  | Diff ->
      (match $3 with 
      | [f; s] -> mk_diff f s
      | _ -> failwith ("Parse error: expected 2 arguments for " ^ (str_of_symbol $2)))
  | sym -> failwith ("Expected function symbol but found " ^ (str_of_symbol sym))
} 
| LPAREN IDENT terms RPAREN {
  (* TODO: check types *)
  let _, res_srt = get_arity_of_symbol (FreeSym $2) in
  mk_app ~srt:res_srt (FreeSym $2) $3
}

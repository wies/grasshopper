%{
open Grass
open Lexing
open SmtLibSyntax

let mk_position s e =
  let start_pos = Parsing.rhs_start_pos s in
  let end_pos = Parsing.rhs_end_pos e in
  { sp_file = start_pos.pos_fname;
    sp_start_line = start_pos.pos_lnum;
    sp_start_col = start_pos.pos_cnum - start_pos.pos_bol;
    sp_end_line = end_pos.pos_lnum;
    sp_end_col = end_pos.pos_cnum - end_pos.pos_bol;
  } 

%}

%token SET_LOGIC SET_OPTION
%token DECLARE_SORT DECLARE_DATATYPES DECLARE_FUN DEFINE_SORT DEFINE_FUN
%token <SmtLibSyntax.symbol> SYMBOL
%token <SmtLibSyntax.sort> SORT
%token <SmtLibSyntax.binder> BINDER
%token BV EXTRACT
%token LET
%token <SmtLibSyntax.ident> IDENT
%token <int> INT
%token <string> STRING
%token ASSERT CHECK_SAT GET_MODEL EXIT
%token SAT UNSAT UNKNOWN ERROR MODEL
%token NAMED BANG LPAREN RPAREN
%token EOF

%start output
%type <SmtLibSyntax.response> output
%%

output:
  SAT { Sat }
| UNSAT { Unsat }
| UNKNOWN { Unknown }
| rcore_or_model  { $1 }
| error { ProgError.syntax_error (mk_position 1 1) None }
;
    
names:
| IDENT names { (Grass.string_of_ident $1) :: $2 }
| /* empty */ { [] }
;

rcore_or_model:
| LPAREN names_or_model RPAREN { $2 }
;

names_or_model:
| names { UnsatCore $1 }
| MODEL cmnd_list_opt { Model $2 }
| ERROR STRING { Error $2 }
    
cmnd:
| DECLARE_SORT IDENT INT { 
  mk_declare_sort ~pos:(mk_position 1 3) $2 $3 
}
| DECLARE_DATATYPES LPAREN RPAREN LPAREN adt_list_opt RPAREN {
  mk_declare_datatypes ~pos:(mk_position 1 6) $5
}
| DECLARE_FUN IDENT LPAREN sort_list_opt RPAREN sort { 
  mk_declare_fun ~pos:(mk_position 1 6) $2 $4 $6
}
| DEFINE_SORT IDENT LPAREN ident_list_opt RPAREN sort {
  mk_define_sort ~pos:(mk_position 1 6) $2 $4 $6
}
| DEFINE_FUN IDENT LPAREN ident_sort_list_opt RPAREN sort term {
  mk_define_fun ~pos:(mk_position 1 7) $2 $4 $6 $7
}
| ASSERT term { 
  mk_assert ~pos:(mk_position 1 2) $2
}
;

cmnd_list:
| LPAREN cmnd RPAREN cmnd_list { $2 :: $4 }
| LPAREN cmnd RPAREN { [$2] }
| term cmnd_list { mk_assert ~pos:(mk_position 1 1) $1 :: $2 }
| term { [mk_assert ~pos:(mk_position 1 1) $1] }
;

cmnd_list_opt:
| cmnd_list { $1 }
| /* empty */ { [] }
  
sort_list_opt:
| sort_list { $1 }
| /* empty */ { [] }

sort_list:
| sort sort_list { $1 :: $2 }
| sort { [$1] }
;

sort: 
| SORT { $1 }
/* TODO bitvector */
| IDENT { FreeSort ($1, []) }
| LPAREN IDENT BV INT RPAREN { assert($2 = ("_",0)); BvSort $4 }
| LPAREN IDENT sort_list RPAREN { FreeSort ($2, $3) }
;

ident_list:
| IDENT ident_list { $1 :: $2 }
| IDENT { [$1] }
;

ident_list_opt:
| ident_list { $1 }
| /* empty */ { [] }
;

ident_sort_list_opt:
| LPAREN IDENT sort RPAREN ident_sort_list_opt { ($2, $3) :: $5 }
| /* empty */ { [] }
;

adt_list_opt:
| LPAREN IDENT adt_constr_list_opt RPAREN adt_list_opt { ($2, $3) :: $5 }
| /* empty */ { [] }
;

adt_constr_list_opt:
| LPAREN IDENT adt_constr_arg_list_opt RPAREN adt_constr_list_opt {
  ($2, $3) :: $5
}
| /* empty */ { [] }
;

adt_constr_arg_list_opt:
| LPAREN IDENT sort RPAREN adt_constr_arg_list_opt { ($2, $3) :: $5 }
| /* empty */ { [] }
;
    
  
symbol:
| SYMBOL { $1 }
| IDENT { Ident $1 }
| LPAREN IDENT EXTRACT INT INT RPAREN { assert($2 = ("_",0)); BvExtract ($4, $5) }
;

term:
| INT { mk_const ~pos:(mk_position 1 1) (IntConst $1) }
| symbol { mk_const ~pos:(mk_position 1 1) $1 }
| LPAREN symbol term_list RPAREN {
  mk_app ~pos:(mk_position 1 4) $2 $3
}
| LPAREN BINDER LPAREN ident_sort_list_opt RPAREN term RPAREN {
  mk_binder ~pos:(mk_position 1 7) $2 $4 $6
}
| LPAREN LET LPAREN def_list_opt RPAREN term RPAREN {
  mk_let ~pos:(mk_position 1 7) $4 $6
}
| LPAREN BANG term NAMED IDENT RPAREN {
  mk_annot ~pos:(mk_position 1 6) $3 (Name $5)
}
;

term_list:
| term term_list { $1 :: $2 }
| term { [$1] }
;

def_list_opt:
| LPAREN IDENT term RPAREN def_list_opt { ($2, $3) :: $5 }
| /* empty */ { [] }

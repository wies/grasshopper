%{
open Form
open Axioms

type def = Term of term | Form of form

let defs : (ident, def) Hashtbl.t = Hashtbl.create 0

let resolve_id_to_term id =
  try 
    match Hashtbl.find defs id with
    | Term t -> t
    | Form _ -> failwith "type error in MSAT formula"
  with Not_found -> mk_const id

let resolve_id_to_form id =
  try
    match Hashtbl.find defs id with
    | Form f -> f
    | Term _ -> failwith "type error in MSAT formula"
  with Not_found -> mk_pred id []

%}

%token <int> NUM
%token <string * int> IDENT
%token <string> NAME
%token EQ
%token LPAREN RPAREN COMMA COLON COLONEQ STAR ARROW
%token AND OR NOT
%token VAR DEFINE FORMULA
%token EOL EOF

%right ARROW
%left STAR
%left OR
%left AND
%right NOT 

%nonassoc EQ 
%nonassoc COMMA 
%nonassoc COLON COLONEQ 
%nonassoc VAR DEFINE FORMULA 

%start main
%type <Form.form> main
%%

main:
| declarations definitions FORMULA iform EOL EOF { Hashtbl.clear defs; $4 }
;
    
declarations:
| declaration declarations { () }
| declaration { () }
;

declaration:
| VAR IDENT COLON type_term EOL { () }
;

type_term:
| NAME { () }
| type_term STAR type_term { () }
| type_term ARROW type_term { () }
;

definitions:
| definitions definition { Hashtbl.add defs (fst $2) (snd $2) }
| definition { Hashtbl.add defs (fst $1) (snd $1) }
;

definition:
| DEFINE IDENT COLONEQ term EOL { ($2, Term $4) }
| DEFINE IDENT COLONEQ form EOL { ($2, Form $4) } 
;

term:
| IDENT { resolve_id_to_term $1 }
| IDENT LPAREN args RPAREN { mk_app $1 $3 }
;

args:
| IDENT { [resolve_id_to_term $1] }
| IDENT COMMA args { resolve_id_to_term $1 :: $3 }
;

form:
| NOT LPAREN iform RPAREN { mk_not $3 }
| LPAREN iform RPAREN { $2 }
;

iform:
| IDENT { resolve_id_to_form $1 }
| term EQ term { 
    match ($1, $3) with
    | FunApp (fn, ts), Const c
    | Const c, FunApp (fn, ts) 
      when is_pred_id fn && c = id_true ->
	mk_pred fn ts
    | FunApp (fn1, ts1), FunApp(fn2, ts2) 
      when is_pred_id fn1 ->
	let p1 = mk_pred fn1 ts1 in
	let p2 = mk_pred fn2 ts2 in
	mk_or [mk_and [p1; p2]; mk_and [mk_not p1; mk_not p2]]
    | t1, t2 -> mk_eq t1 t2 
  } 
| iform AND iform { smk_and [$1; $3] }
| iform OR iform { mk_or [$1; $3] }
;

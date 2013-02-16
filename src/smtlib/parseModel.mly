%{
open Form

let parse_error = ParseError.parse_error

let process_definition m def =
  let sym = fst def in
  match snd def with
     | (arity, _) :: _ ->
	 List.fold_right 
	   (fun (_, defs) -> Model.add_def sym defs) 
	   (snd def) 
	   (Model.add_decl sym arity m)
     | [] -> m

%}

%token <Form.symbol> SYMBOL
%token <Form.sort * Form.symbol> VAL
%token LBRACE RBRACE ARROW ELSE
%token UNSPEC
%token EOF
%start main
%type <Model.model> main
%%

   
main:
  definition main { process_definition $2 $1 }
| definition EOF { process_definition Model.empty $1 }
;

definition:
  SYMBOL ARROW VAL { ($1, [(([], fst $3), ([], snd $3))]) }
| SYMBOL ARROW LBRACE mappings RBRACE { ($1, $4) }
; 

mappings:
  mapping mappings { $1 :: $2 }
| ELSE ARROW UNSPEC { [] }
| UNSPEC { [] }
;

mapping:
| args ARROW VAL { ((fst $1, fst $3), (snd $1, snd $3)) }
;

args:
  VAL args { (fst $1 :: fst $2, snd $1 :: snd $2) }
| VAL { ([fst $1], [snd $1]) }
;


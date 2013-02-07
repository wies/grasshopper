%{
open Form

let parse_error = ParseError.parse_error
%}

%token <string * int> IDENT
%token <int> ELEM
%token <bool> BOOL
%token LBRACE RBRACE ARROW ELSE
%token UNSPEC
%token EOF
%start main
%type <Model.model> main
%%

   
main:
  definition main { List.fold_right (Model.add_def (fst $1)) (snd $1) $2 }
| definition EOF {List.fold_right (Model.add_def (fst $1)) (snd $1) Model.empty}
;

definition:
  IDENT ARROW ELEM { (FreeSym $1, [([], Model.Int $3)]) }
| IDENT ARROW BOOL { (FreeSym $1, [([], Model.Bool $3)]) }
| IDENT ARROW LBRACE mappings RBRACE { (FreeSym $1, $4) }
; 

mappings:
  mapping mappings { $1 :: $2 }
| ELSE ARROW UNSPEC { [] }
| UNSPEC { [] }
;

mapping:
  args ARROW BOOL { ($1, Model.Bool $3) }
| args ARROW ELEM { ($1, Model.Int $3) }
;

args:
  ELEM args { $1 :: $2 }
| ELEM { [$1] }
;


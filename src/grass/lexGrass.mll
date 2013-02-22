{
open Form
open ParseGrass

let keyword_table = Hashtbl.create 32
let _ =
  List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
    (["set-logic", SET_LOGIC;
      "set-option", SET_OPTION;
      (* declarations and definitions *)
      "declare-sort", DECLARE_SORT;
      "declare-fun", DECLARE_FUN;
      (* sorts *)
      bool_sort_string, BOOL_SORT;
      loc_sort_string, LOC_SORT;
      fld_sort_string, FLD_SORT;
      set_sort_string, SET_SORT;
      (* formula constructors *)
      "forall", BINDER(Forall);
      "exists", BINDER(Exists);
      "and", BOOLOP(And);
      "or", BOOLOP(Or);
      "not", BOOLOP(Not);
      (* values *)
      "true", BOOL_VAL(true);
      "false", BOOL_VAL(false);
      (* commands *)
      "assert", ASSERT;
      "check-sat", CHECK_SAT;
      "get-model", GET_MODEL;
      "exit", EXIT;
      (* other *)
      ":named", NAMED;
    ] @ 
    (* term constructors *)
    List.map (fun sym -> str_of_symbol sym, SYMBOL(sym))
      [Null; Read; Write; EntPnt; Empty; SetEnum; Union; Inter; Diff;
       ReachWO; Elem; SubsetEq; Frame])
}

let digitchar = ['0'-'9']
let idchar = ['a'-'z' 'A'-'Z' '?' '$' '.']
let kwchar = idchar | '_' | ':' | '-'
 
rule token = parse
  [' ' '\t' '\n'] { token lexbuf }
| "//" [^ '\n']* {token lexbuf }
| '=' { SYMBOL(Eq) }
| '!' { BANG }
| '(' { LPAREN }
| ')' { RPAREN }
| ('-'? digitchar*) as num { INT_VAL(int_of_string num) }
| idchar* as name '_' (digitchar* as num) { IDENT(name, int_of_string num) }
| kwchar* as kw
    { try
        Hashtbl.find keyword_table kw
      with Not_found ->
        IDENT (kw, 0)
    }
| eof { EOF }

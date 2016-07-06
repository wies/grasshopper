{
open Grass
open Lexing
open SmtLibSyntax
open SmtLibParser

let set_file_name lexbuf name =
   lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = name }

let keyword_table = Hashtbl.create 48
let _ =
  List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
    (["set-logic", SET_LOGIC;
      "set-option", SET_OPTION;
      (* declarations and definitions *)
      "declare-sort", DECLARE_SORT;
      "declare-fun", DECLARE_FUN;
      "define-sort", DEFINE_SORT;
      "define-fun", DEFINE_FUN;
      (* sorts *)
      Grass.bool_sort_string, SORT(BoolSort);
      Grass.int_sort_string, SORT(IntSort);
      "BitVec", BV;
      (* term constructors *)
      "forall", BINDER(Forall);
      "exists", BINDER(Exists);
      "and", SYMBOL(And);
      "or", SYMBOL(Or);
      "not", SYMBOL(Not);
      "ite", SYMBOL(Ite);
      "bvnot", SYMBOL(BvNot);
      "bvand", SYMBOL(BvAnd);
      "bvor", SYMBOL(BvOr);
      "bvult", SYMBOL(BvUlt);
      "bvslt", SYMBOL(BvSlt);
      "bvsle", SYMBOL(BvSle);
      "bvsgt", SYMBOL(BvSgt);
      "bvsge", SYMBOL(BvSge);
      "bvneg", SYMBOL(BvNeg);
      "bvadd", SYMBOL(BvAdd);
      "bvmul", SYMBOL(BvMul);
      "bvudiv", SYMBOL(BvUdiv);
      "bvurem", SYMBOL(BvUrem);
      "bvshl", SYMBOL(BvShl);
      "bvshr", SYMBOL(BvShr);
      "concat", SYMBOL(BvConcat);
      "extract", EXTRACT;
      "let", LET;
      (* values *)
      "true", SYMBOL(BoolConst true);
      "false", SYMBOL(BoolConst false);
      (* commands *)
      "assert", ASSERT;
      "check-sat", CHECK_SAT;
      "get-model", GET_MODEL;
      "exit", EXIT;
      (* responses *)
      "sat", SAT;
      "unsat", UNSAT;
      "unknown", UNKNOWN;
      "error", ERROR;
      "model", MODEL;
      (* other *)
      ":named", NAMED;
    ])
}

let digitchar = ['0'-'9']
let identchar = ['a'-'z' 'A'-'Z' '?' '$' '.' '@' '_' '#' '^']
let ident = identchar (identchar | digitchar | ':' | '-' | '!')*
 
rule token = parse
  [' ' '\t'] { token lexbuf }
| "\r\n" { Lexing.new_line lexbuf; token lexbuf }
| '\n' { Lexing.new_line lexbuf; token lexbuf }
| ";" [^ '\n']* {token lexbuf }
| "=>" { SYMBOL(Impl) }
| '=' { SYMBOL(Eq) }
| "<=" { SYMBOL(Leq) }
| ">=" { SYMBOL(Geq) }
| '<' { SYMBOL(Lt) }
| '>' { SYMBOL(Gt) }
| '+' { SYMBOL(Plus) }
| '-' { SYMBOL(Minus) }
| '*' { SYMBOL(Mult) }
| '/' { SYMBOL(Div) }
| '!' { BANG }
| '(' { LPAREN }
| ')' { RPAREN }
| "#b" (('0' | '1')* as bits) { INT (int_of_bits bits) }
| "#x" (['A'-'F''a'-'f''0'-'9']* as hex) { INT (Int64.to_int (SplLexer.hexa_to_int hex)) }
| ('-'? digitchar*) as num { INT(int_of_string num) }
| ident as name '^' (digitchar* as num) { IDENT(name, if num <> "" then int_of_string num else 0) }
| ident as kw
    { try
        Hashtbl.find keyword_table kw
      with Not_found ->
        IDENT(kw, 0)
    }
| '"' [^'"']* as str '"' { STRING(str) }
| eof { EOF }
| _ { let pos = lexeme_start_p lexbuf in 
      let spos = 
        { sp_file = pos.pos_fname;
          sp_start_line = pos.pos_lnum;
          sp_start_col = pos.pos_cnum - pos.pos_bol;
          sp_end_line = pos.pos_lnum;
          sp_end_col = pos.pos_cnum - pos.pos_bol;
        } 
      in
      ProgError.lexical_error spos
    }

(** SMT-LIB v2 abstract syntax *)

type ident = Form.ident

type pos = Prog.source_position

type sort = 
  | IntSort | BoolSort
  | FunSort of sort list * sort
  | FreeSort of ident * sort list

type symbol =
  | BoolConst of bool
  | IntConst of int
  | Ident of ident
  | Minus | Plus | Mult | Div
  | Eq | Gt | Lt | Geq | Leq
  | And | Or | Impl | Not

type annotation =
  | Name of ident

type binder = Exists | Forall | Lambda

type term =
  | App of symbol * term list * pos option
  | Binder of binder * (ident * sort) list * term * pos option
  | Annot of term * annotation * pos option

type command =
  | DeclareSort of ident * int * pos option
  | DefineSort of ident * ident list * sort * pos option
  | DeclareFun of ident * sort * pos option
  | DefineFun of ident * term * pos option
  | Assert of term * pos option

type response =
  | Sat
  | Unsat
  | Unknown
  | Model of command list
  | UnsatCore of string list
  | Error of string

(** constructor functions *)

let mk_const ?pos sym = App (sym, [], pos)

let mk_app ?pos sym ts = App (sym, ts, pos)

let mk_binder ?pos b vs t = Binder (b, vs, t, pos)

let mk_annot ?pos t a = Annot (t, a, pos)

let mk_declare_sort ?pos id arity = DeclareSort (id, arity, pos)

let mk_declare_fun ?pos id srt = DeclareFun (id, srt, pos)

let mk_define_sort ?pos id args srt = DefineSort (id, args, srt, pos)

let mk_define_fun ?pos id t = DefineFun (id, t, pos)

let mk_assert ?pos t = Assert (t, pos)

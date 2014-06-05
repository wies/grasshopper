(** SMT-LIB v2 abstract syntax *)

type ident = Form.ident

type pos = Prog.source_position

type sort = 
  | IntSort | BoolSort
  | FunSort of sort list * sort
  | FreeSort of ident * sort list

type symbol =
  | BoolConst of bool
  | FreeSym of ident
  | Minus | Plus | Mult | Div
  | Eq | Gt | Lt | Geq | Leq
  | And | Or | Impl | Not

type annotation
  | Name of string

type binder = Exists | Forall | Lambda

type term =
  | Var of ident * sort
  | App of symbol * term list * sort
  | Binder of binder * (ident * sort) list * form * sort
  | Annot of annotation

type command =
  | DeclareSort of ident * int
  | DefineSort of ident * sort
  | DeclareFun of ident * sort
  | DefineFun of ident * term
  | Assert of term
  | Model of command list



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
  | Var of ident * sort * pos
  | App of symbol * term list * sort * pos
  | Binder of binder * (ident * sort) list * form * sort * pos
  | Annot of annotation * pos

type command =
  | DeclareSort of ident * int * pos
  | DefineSort of ident * sort * pos
  | DeclareFun of ident * sort * pos
  | DefineFun of ident * term * pos
  | Assert of term * pos 
  | Model of command list * pos



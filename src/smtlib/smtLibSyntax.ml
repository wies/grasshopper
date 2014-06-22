(** SMT-LIB v2 abstract syntax *)

type ident = Form.ident

type pos = Form.source_position

type sort = 
  | IntSort | BoolSort
  | FreeSort of ident * sort list

type symbol =
  | BoolConst of bool
  | IntConst of int
  | Ident of ident
  | Minus | Plus | Mult | Div
  | Eq | Gt | Lt | Geq | Leq
  | And | Or | Impl | Not | Ite

type annotation =
  | Name of ident

type binder = Exists | Forall

type term =
  | App of symbol * term list * pos option
  | Binder of binder * (ident * sort) list * term * pos option
  | Annot of term * annotation * pos option

type command =
  | DeclareSort of ident * int * pos option
  | DefineSort of ident * ident list * sort * pos option
  | DeclareFun of ident * sort list * sort * pos option
  | DefineFun of ident * (ident * sort) list * sort * term * pos option
  | Assert of term * pos option

type response =
  | Sat
  | Unsat
  | Unknown
  | Model of command list
  | UnsatCore of string list
  | Error of string

(** Constructor functions *)

let mk_const ?pos sym = App (sym, [], pos)

let mk_app ?pos sym ts = 
  match sym, ts with
  | Minus, [App (IntConst i, [], _)] -> 
      App (IntConst (-i), [], pos)
  | _, _ -> 
      App (sym, ts, pos)

let mk_binder ?pos b vs t = Binder (b, vs, t, pos)

let mk_annot ?pos t a = Annot (t, a, pos)

let mk_declare_sort ?pos id arity = DeclareSort (id, arity, pos)

let mk_declare_fun ?pos id arg_srts res_srt = DeclareFun (id, arg_srts, res_srt, pos)

let mk_define_sort ?pos id args srt = DefineSort (id, args, srt, pos)

let mk_define_fun ?pos id args res_srt t = DefineFun (id, args, res_srt, t, pos)

let mk_assert ?pos t = Assert (t, pos)

(** Utility functions *)

let idents_in_term t =
  let rec iot acc = function
    | App (sym, ts, _) -> 
        let acc1 = match sym with
        | Ident id -> Form.IdSet.add id acc
        | _ -> acc
        in
        List.fold_left iot acc1 ts
    | Binder (_, vs, t, _) ->
        let acc1 = List.fold_left (fun acc1 (id, _) -> Form.IdSet.add id acc1) acc vs in
        iot acc1 t
    | Annot (t, _, _) -> iot acc t
  in iot Form.IdSet.empty t

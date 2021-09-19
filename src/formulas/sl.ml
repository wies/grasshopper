(** Abstract syntax tree for separation logic formulas *)

type ident = Grass.ident
type sort = Grass.sort
type bool_op = Grass.bool_op
type binder = Grass.binder
type source_position = Grass.source_position

let mk_ident = GrassUtil.mk_ident
module IdMap = Grass.IdMap
module IdSet = Grass.IdSet
module SortMap = Grass.SortMap
module SortSet = Grass.SortSet
let ident_to_string = Grass.string_of_ident

(*deprecated?*)
(*let to_field f = GrassUtil.mk_free_const (GrassUtil.field_sort Grass.Loc) f*)

type pred_symbol =
  | Emp
  | Region
  | Pred of ident

type sep_op =
  | SepStar | SepPlus | SepIncl

type form =
  | Pure of Grass.form * source_position option
  | Atom of pred_symbol * Grass.term list * source_position option
  | SepOp of sep_op * form * form * source_position option
  | BoolOp of bool_op * form list * source_position option
  | Binder of binder * (ident * sort) list * form * source_position option
  | Ite of Grass.form * form * form * source_position option

module SlSet = Set.Make(struct
    type t = form
    let compare = compare
  end)

module SlMap = Map.Make(struct
    type t = form
    let compare = compare
  end)

(** Pretty printing *)

open Format

let rec pr_form ppf = function
  | Pure (p, _) -> Grass.pr_form ppf p
  | BoolOp (Grass.Not, fs, _) -> pr_not ppf (List.hd fs)
  | BoolOp (Grass.And, fs, _) -> pr_ands ppf fs
  | BoolOp (Grass.Or, fs, _) -> pr_ors ppf fs
  | SepOp (SepStar, f1, f2, _) -> pr_sep_star ppf [f1; f2]
  | SepOp (SepPlus, f1, f2, _) -> pr_sep_plus ppf [f1; f2]
  | SepOp (SepIncl, f1, f2, _) -> 
      fprintf ppf "@[<2>%a@] -**@ %a" pr_form f1 pr_form f2
  | Atom (Emp, _, _) -> fprintf ppf "emp"
  | Atom (Region, [o; f], _) ->
      fprintf ppf "acc(%a.@[%a@])" Grass.pr_term o Grass.pr_term f 
  | Atom (Region, [r], _) -> 
      (match r with
      | Grass.App (Grass.SetEnum, [t], _) ->
          fprintf ppf "acc(@[%a@])" Grass.pr_term t
      | _ ->
          fprintf ppf "acc(@[%a@])" Grass.pr_term r)
  | Atom (Region, _, _) -> ()
  | Atom (Pred p, ts, _) ->
      fprintf ppf "%a(@[%a@])" Grass.pr_ident p Grass.pr_term_list ts
  | Binder (b, vs, f, _) ->
      fprintf ppf "@[(%a)@]" pr_quantifier (b, vs, f)
  | Ite (cond, f1, f2, _) -> fprintf ppf "ite(@[%a@], @[%a@], @[%a@])" Grass.pr_form cond pr_form f1 pr_form f2

and pr_sep_star ppf = function
  | [] -> fprintf ppf "%s" "emp"
  | [f] -> fprintf ppf "@[<2>%a@]" pr_form f
  | (BoolOp (Grass.Or, _, _) as f) :: fs 
  | (BoolOp (Grass.And, _, _) as f) :: fs
  | (SepOp (SepPlus, _, _, _) as f) :: fs
  | (SepOp (SepIncl, _, _, _) as f) :: fs
  | (Binder _ as f) :: fs -> fprintf ppf "(@[<2>%a@]) &*&@ %a" pr_form f pr_sep_star fs
  | f :: fs -> fprintf ppf "@[<2>%a@] &*&@ %a" pr_form f pr_sep_star fs

and pr_sep_plus ppf = function
  | [] -> fprintf ppf "%s" "emp"
  | [f] -> fprintf ppf "@[<2>%a@]" pr_form f
  | (BoolOp (Grass.Or, _, _) as f) :: fs 
  | (BoolOp (Grass.And, _, _) as f) :: fs
  | (SepOp (SepIncl, _, _, _) as f) :: fs
  | (Binder _ as f) :: fs -> fprintf ppf "(@[<2>%a@]) &+&@ %a" pr_form f pr_sep_plus fs
  | f :: fs -> fprintf ppf "@[<2>%a@] &+&@ %a" pr_form f pr_sep_plus fs

and pr_ands ppf = function
  | [] -> fprintf ppf "%s" "true"
  | [f] -> fprintf ppf "@[<2>%a@]" pr_form f
  | (BoolOp (Grass.Or, _, _) as f) :: fs
  | (Binder _ as f) :: fs -> fprintf ppf "(@[<2>%a@]) &&@ %a" pr_form f pr_ands fs
  | f :: fs -> fprintf ppf "@[<2>%a@] &&@ %a" pr_form f pr_ands fs

and pr_ors ppf = function
  | [] -> fprintf ppf "%s" "false"
  | [f] -> fprintf ppf "@[<2>%a@]" pr_form f
  | (Binder _ as f) :: fs -> fprintf ppf "(@[<2>%a@]) &&@ %a" pr_form f pr_ors fs
  | f :: fs -> fprintf ppf "@[<2>%a@] ||@ %a" pr_form f pr_ors fs

and pr_not ppf = function
  | (Atom (Emp, _, _) as f)
  | (Atom (Pred _, _, _) as f) -> fprintf ppf "!@[<2>%a@]" pr_form f
  | f -> fprintf ppf "!(@[<3>%a@])" pr_form f

and pr_quantifier ppf = function
  | (_, [], f) -> fprintf ppf "%a" pr_form f
  | (b, vs, f) -> fprintf ppf "@[<2>%a @[%a@] ::@ %a@]" Grass.pr_binder b Grass.pr_vars vs pr_form f

let print_form out_ch f = 
  fprintf (formatter_of_out_channel out_ch) "%a@\n@?" pr_form f

let string_of_form f = pr_form str_formatter f; flush_str_formatter ()



(** Abstract syntax tree for separation logic formulas *)

type ident = Form.ident
type sort = Form.sort
type bool_op = Form.bool_op
type binder = Form.binder
type source_position = Form.source_position

let mk_ident = FormUtil.mk_ident
module IdMap = Form.IdMap
module IdSet = Form.IdSet
let ident_to_string = Form.string_of_ident

let to_field f = FormUtil.mk_free_const (Form.Fld Form.Loc) f

type pred_symbol =
  | Emp
  | Region
  | Pred of ident

type sep_op =
  | SepStar | SepPlus | SepIncl
  
type form =
  | Pure of Form.form * source_position option
  | Atom of pred_symbol * Form.term list * source_position option
  | SepOp of sep_op * form * form * source_position option
  | BoolOp of bool_op * form list * source_position option
  | Binder of binder * (ident * sort) list * form * source_position option

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
  | Pure (p, _) -> Form.pr_form ppf p
  | BoolOp (Form.Not, fs, _) -> pr_not ppf (List.hd fs)
  | BoolOp (Form.And, fs, _) -> pr_ands ppf fs
  | BoolOp (Form.Or, fs, _) -> pr_ors ppf fs
  | SepOp (SepStar, f1, f2, _) -> pr_sep_star ppf [f1; f2]
  | SepOp (SepPlus, f1, f2, _) -> pr_sep_plus ppf [f1; f2]
  | SepOp (SepIncl, f1, f2, _) -> 
      fprintf ppf "@[<2>%a@] -**@ %a" pr_form f1 pr_form f2
  | Atom (Emp, _, _) -> fprintf ppf "emp"
  | Atom (Region, [r], _) -> 
      (match r with
      | Form.App (Form.SetEnum, [t], _) ->
          fprintf ppf "acc(@[%a@])" Form.pr_term t
      | _ ->
          fprintf ppf "acc(@[%a@])" Form.pr_term r)
  | Atom (Region, _, _) -> ()
  | Atom (Pred p, ts, _) ->
      fprintf ppf "%a(@[%a@])" Form.pr_ident p Form.pr_term_list ts
  | Binder (b, vs, f, _) ->
      fprintf ppf "@[(%a)@]" pr_quantifier (b, vs, f)

and pr_sep_star ppf = function
  | [] -> fprintf ppf "%s" "emp"
  | [f] -> fprintf ppf "@[<2>%a@]" pr_form f
  | (BoolOp (Form.Or, _, _) as f) :: fs 
  | (BoolOp (Form.And, _, _) as f) :: fs
  | (SepOp (SepPlus, _, _, _) as f) :: fs
  | (SepOp (SepIncl, _, _, _) as f) :: fs
  | (Binder _ as f) :: fs -> fprintf ppf "(@[<2>%a@]) &*&@ %a" pr_form f pr_sep_star fs
  | f :: fs -> fprintf ppf "@[<2>%a@] &*&@ %a" pr_form f pr_sep_star fs

and pr_sep_plus ppf = function
  | [] -> fprintf ppf "%s" "emp"
  | [f] -> fprintf ppf "@[<2>%a@]" pr_form f
  | (BoolOp (Form.Or, _, _) as f) :: fs 
  | (BoolOp (Form.And, _, _) as f) :: fs
  | (SepOp (SepIncl, _, _, _) as f) :: fs
  | (Binder _ as f) :: fs -> fprintf ppf "(@[<2>%a@]) &+&@ %a" pr_form f pr_sep_plus fs
  | f :: fs -> fprintf ppf "@[<2>%a@] &+&@ %a" pr_form f pr_sep_plus fs

and pr_ands ppf = function
  | [] -> fprintf ppf "%s" "true"
  | [f] -> fprintf ppf "@[<2>%a@]" pr_form f
  | (BoolOp (Form.Or, _, _) as f) :: fs
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
  | (b, vs, f) -> fprintf ppf "@[<2>%a @[%a@] ::@ %a@]" Form.pr_binder b Form.pr_vars vs pr_form f

let print_form out_ch f = 
  fprintf (formatter_of_out_channel out_ch) "%a@\n@?" pr_form f

let string_of_form f = pr_form str_formatter f; flush_str_formatter ()


